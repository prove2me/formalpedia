-- Prove2me | solution 1 for GraphSimOT.Gaps.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:53:30.211413+00:00
-- url     : https://prove2.me/submissions/72f6e845-f3c4-4161-b362-d56a5482c13a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Theorems.Thm_GraphSimOT_Gaps_theorem_6
import Theorems.Thm_GraphSimOT_Gaps_theorem_9
import Theorems.Thm_GraphSimOT_Gaps_theorem_11
import Theorems.Thm_GraphSimOT_Gaps_theorem_14

open Matrix GraphSimOT.Gaps

namespace Theorem2Aux

lemma edNorm_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    0 ≤ edNorm A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma deltaOTEd_nonneg {n : ℕ} (G H : SimpleGraph (Fin n)) : 0 ≤ deltaOTEd G H := by
  apply Real.sInf_nonneg
  rintro _ ⟨Q, -, rfl⟩
  exact edNorm_nonneg _

lemma dOTEd_le_sq_mul_deltaOTEd {n : ℕ} (hn : n ≠ 0) (G H : SimpleGraph (Fin n)) :
    dOTEd G H ≤ (n : ℝ) ^ 2 * deltaOTEd G H := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hDS_ne : (DSstar n).Nonempty := by
    refine ⟨(1 / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ), ?_, ?_, ?_⟩
    · intro i j
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> positivity
    · intro i
      simp [Matrix.one_apply]
    · intro j
      simp [Matrix.one_apply]
  rw [← div_le_iff₀' hn2]
  apply le_csInf (hDS_ne.image _)
  rintro _ ⟨Qstar, hQstar, rfl⟩
  rw [div_le_iff₀' hn2]
  let Q : Matrix (Fin n) (Fin n) ℝ := (n : ℝ) • Qstar
  have hQ : Q ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => mul_nonneg hnR.le (hQstar.1 i j), ?_, ?_⟩
    · intro i
      simp only [Q, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.1 i]
      exact mul_one_div_cancel hnR.ne'
    · intro j
      simp only [Q, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, hQstar.2.2 j]
      exact mul_one_div_cancel hnR.ne'
  have hcost : costEd G H Q = (n : ℝ) ^ 2 * costEd G H Qstar := by
    unfold costEd edNorm Bmat
    simp only [Q, Matrix.smul_apply, smul_eq_mul]
    have hterm : ∀ a b : Fin n × Fin n,
        |((n : ℝ) * Qstar a.1 a.2) * disc G H a b * ((n : ℝ) * Qstar b.1 b.2)| =
          (n : ℝ) ^ 2 * |Qstar a.1 a.2 * disc G H a b * Qstar b.1 b.2| := by
      intro a b
      calc
        |((n : ℝ) * Qstar a.1 a.2) * disc G H a b * ((n : ℝ) * Qstar b.1 b.2)|
            = |(n : ℝ) ^ 2 * (Qstar a.1 a.2 * disc G H a b * Qstar b.1 b.2)| := by ring_nf
        _ = (n : ℝ) ^ 2 * |Qstar a.1 a.2 * disc G H a b * Qstar b.1 b.2| := by
            rw [abs_mul, abs_of_pos hn2]
    simp_rw [hterm, ← Finset.mul_sum]
  have hbdd : BddBelow (costEd G H '' (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨M, -, rfl⟩
    exact edNorm_nonneg _
  exact (csInf_le hbdd ⟨Q, hQ, rfl⟩).trans_eq hcost

lemma part1 (n : ℕ) (G H : SimpleGraph (Fin n)) : deltaEd G H ≤ 2 * deltaOTEd G H := by
  by_cases hn : n = 0
  · subst hn
    have h0 : deltaEd G H = 0 := by simp [deltaEd]
    rw [h0]
    linarith [deltaOTEd_nonneg G H]
  · have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [deltaEd, div_le_iff₀ hn2]
    have h6 := theorem_6.2 n G H
    have hd := dOTEd_le_sq_mul_deltaOTEd hn G H
    linarith

lemma opNorm_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (p q : ℝ) (A : Matrix ι κ ℝ) :
    0 ≤ opNorm p q A := by
  apply Real.sSup_nonneg
  rintro _ ⟨x, -, rfl⟩
  unfold lpNorm
  positivity

lemma deltaOT2_nonneg {n : ℕ} (G H : SimpleGraph (Fin n)) : 0 ≤ deltaOT2 G H := by
  apply Real.sInf_nonneg
  rintro _ ⟨Q, -, rfl⟩
  exact opNorm_nonneg 2 2 _

lemma opNorm_two_le_card {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, |M i j| ≤ 1) : opNorm 2 2 M ≤ n := by
  apply Real.sSup_le _ (Nat.cast_nonneg n)
  rintro _ ⟨x, hx, rfl⟩
  have hsum_x : ∑ j : Fin n, x j ^ 2 = 1 := by
    have hx1 : (∑ j : Fin n, |x j| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = 1 := hx
    have hnn : 0 ≤ ∑ j : Fin n, |x j| ^ (2 : ℝ) :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _
    have hsq : ∑ j : Fin n, |x j| ^ (2 : ℝ) = 1 := by
      calc
        ∑ j : Fin n, |x j| ^ (2 : ℝ)
            = ((∑ j : Fin n, |x j| ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by
              rw [← Real.rpow_mul hnn]; norm_num
        _ = 1 := by rw [hx1]; norm_num
    simpa [Real.rpow_two, sq_abs] using hsq
  have hrow : ∀ i : Fin n, |(M *ᵥ x) i| ^ (2 : ℝ) ≤ n := by
    intro i
    rw [Real.rpow_two, sq_abs]
    calc
      (M *ᵥ x) i ^ 2 = (∑ j : Fin n, M i j * x j) ^ 2 := by simp [Matrix.mulVec, dotProduct]
      _ ≤ (∑ j : Fin n, M i j ^ 2) * (∑ j : Fin n, x j ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) x
      _ ≤ (∑ _j : Fin n, (1 : ℝ)) * 1 := by
          rw [hsum_x]
          gcongr with j
          rw [← sq_abs]
          nlinarith [hM i j, abs_nonneg (M i j)]
      _ = n := by simp
  have hsum_Mx : ∑ i : Fin n, |(M *ᵥ x) i| ^ (2 : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
    calc
      ∑ i : Fin n, |(M *ᵥ x) i| ^ (2 : ℝ) ≤ ∑ _i : Fin n, (n : ℝ) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = (n : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        simp [sq]
  unfold lpNorm
  calc
    (∑ i : Fin n, |(M *ᵥ x) i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        ≤ ((n : ℝ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
          gcongr
    _ = n := by
          rw [← Real.rpow_mul (Nat.cast_nonneg n)]
          norm_num

lemma delta2_le_one {n : ℕ} (G H : SimpleGraph (Fin n)) : delta2 G H ≤ 1 := by
  unfold delta2 deltaOp
  have hexp : (1 : ℝ) / 2 + 1 - 1 / 2 = 1 := by ring
  rw [hexp, Real.rpow_one]
  by_cases hn : n = 0
  · subst hn; simp
  · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [div_le_one hnR]
    unfold dOp
    refine (Finset.inf'_le _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).trans ?_
    apply opNorm_two_le_card
    intro i j
    simp only [Matrix.sub_apply, permAdj, adj]
    split_ifs <;> norm_num

lemma part4 (n : ℕ) (G H : SimpleGraph (Fin n)) :
    delta2 G H ≤ (1 + 2 * Real.sqrt 2) * Real.sqrt (deltaOT2 G H) := by
  have h0 : 0 ≤ deltaOT2 G H := deltaOT2_nonneg G H
  by_cases h1 : deltaOT2 G H ≤ 1
  · have h14 := theorem_14 G H
    have hsq : deltaOT2 G H ≤ Real.sqrt (deltaOT2 G H) := by
      have hs0 : 0 ≤ Real.sqrt (deltaOT2 G H) := Real.sqrt_nonneg _
      have hs1 : Real.sqrt (deltaOT2 G H) ≤ 1 := by
        simpa using Real.sqrt_le_sqrt h1
      calc
        deltaOT2 G H = Real.sqrt (deltaOT2 G H) * Real.sqrt (deltaOT2 G H) :=
          (Real.mul_self_sqrt h0).symm
        _ ≤ 1 * Real.sqrt (deltaOT2 G H) :=
          mul_le_mul_of_nonneg_right hs1 hs0
        _ = Real.sqrt (deltaOT2 G H) := one_mul _
    have hmul : Real.sqrt (2 * deltaOT2 G H) = Real.sqrt 2 * Real.sqrt (deltaOT2 G H) :=
      Real.sqrt_mul (by norm_num) _
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (deltaOT2 G H)]
  · have h1' : 1 < deltaOT2 G H := lt_of_not_ge h1
    have hs1 : 1 ≤ Real.sqrt (deltaOT2 G H) := by
      simpa using Real.sqrt_le_sqrt h1'.le
    have hd1 : delta2 G H ≤ 1 := delta2_le_one G H
    have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith

end Theorem2Aux

theorem solution :
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)), deltaEd G H ≤ 2 * deltaOTEd G H) ∧
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      delta1 G H ≤ 15 * Real.sqrt (deltaOT1 G H * Real.log (4 / deltaOT1 G H))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      deltaCut G H ≤ C * deltaOTCut G H ^ (1 - ε)) ∧
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      delta2 G H ≤ (1 + 2 * Real.sqrt 2) * Real.sqrt (deltaOT2 G H)) :=
  ⟨Theorem2Aux.part1, fun _ G H => theorem_9 G H, theorem_11.2, Theorem2Aux.part4⟩
