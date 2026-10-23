-- Prove2me | solution 1 for LinearPriceRule.Concave.rectangle_sharp
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:42:08.939721+00:00
-- url     : https://prove2.me/submissions/700a84d6-7d19-4b96-86c8-914429a148e1

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave.RectangleProof

lemma demand_eq_Qmax (M : Market) (hM : M.Standing)
    (hrect : ∀ Q ∈ Set.Icc 0 M.Qmax, M.PA Q = M.Pm) {p : ℝ} (hp : p ≤ M.Pm) :
    demandAt M p = M.Qmax := by
  have htop : M.Qmax ∈ {Q : ℝ | Q ∈ Set.Icc 0 M.Qmax ∧ p ≤ M.PA Q} := by
    refine ⟨⟨hM.Qmax_pos.le,le_rfl⟩,?_⟩
    rw [hrect M.Qmax ⟨hM.Qmax_pos.le,le_rfl⟩]
    exact hp
  have hbound : BddAbove {Q : ℝ | Q ∈ Set.Icc 0 M.Qmax ∧ p ≤ M.PA Q} :=
    ⟨M.Qmax,fun _ hQ => hQ.1.2⟩
  exact le_antisymm (csSup_le ⟨M.Qmax,htop⟩ (fun _ hQ => hQ.1.2))
    (le_csSup hbound htop)

lemma Qmax_optimal (M : Market) (hM : M.Standing)
    (hrect : ∀ Q ∈ Set.Icc 0 M.Qmax, M.PA Q = M.Pm) : IsOptQty M M.Qmax := by
  refine ⟨⟨hM.Qmax_pos.le,le_rfl⟩,?_⟩
  intro Q hQ
  simp only [profit,hrect Q hQ,hrect M.Qmax ⟨hM.Qmax_pos.le,le_rfl⟩]
  exact mul_le_mul_of_nonneg_left hQ.2 (sub_nonneg.mpr hM.c_lt_Pm.le)

lemma optimal_eq_Qmax (M : Market) (hM : M.Standing)
    (hrect : ∀ Q ∈ Set.Icc 0 M.Qmax, M.PA Q = M.Pm) {Q : ℝ} (hQ : IsOptQty M Q) :
    Q=M.Qmax := by
  have h := hQ.2 M.Qmax ⟨hM.Qmax_pos.le,le_rfl⟩
  simp only [profit,hrect Q hQ.1,hrect M.Qmax ⟨hM.Qmax_pos.le,le_rfl⟩] at h
  exact le_antisymm hQ.1.2 (le_of_mul_le_mul_left h (sub_pos.mpr hM.c_lt_Pm))

lemma linProfit_eq (M : Market) (hM : M.Standing)
    (hrect : ∀ Q ∈ Set.Icc 0 M.Qmax, M.PA Q = M.Pm) :
    linProfit M = (M.Pm-M.c)*M.Qmax/2 := by
  have hp : linPrice M ≤ M.Pm := by dsimp [linPrice]; linarith [hM.c_lt_Pm]
  rw [linProfit,demand_eq_Qmax M hM hrect hp]
  dsimp [linPrice]
  ring

end LinearPriceRule.Concave.RectangleProof

open LinearPriceRule.Concave

theorem solution (M : Market) (hM : M.Standing)
    (hrect : ∀ Q ∈ Set.Icc 0 M.Qmax, M.PA Q = M.Pm) :
    IsOptQty M M.Qmax ∧
    (∀ Q, IsOptQty M Q → profit M Q / linProfit M = 2) ∧
    (M.c = 0 → ∀ Q, IsOptQty M Q → M.PA Q / linPrice M = 2) := by
  have hprofit : 0 < linProfit M := by
    rw [RectangleProof.linProfit_eq M hM hrect]
    exact div_pos (mul_pos (sub_pos.mpr hM.c_lt_Pm) hM.Qmax_pos) (by norm_num)
  have hprice : 0 < linPrice M := by
    dsimp [linPrice]
    linarith [hM.c_nonneg,hM.c_lt_Pm]
  refine ⟨RectangleProof.Qmax_optimal M hM hrect,?_,?_⟩
  · intro Q hQ
    rw [RectangleProof.optimal_eq_Qmax M hM hrect hQ]
    apply (div_eq_iff (ne_of_gt hprofit)).mpr
    rw [profit,hrect M.Qmax ⟨hM.Qmax_pos.le,le_rfl⟩,
      RectangleProof.linProfit_eq M hM hrect]
    ring
  · intro hc Q hQ
    rw [hrect Q hQ.1]
    apply (div_eq_iff (ne_of_gt hprice)).mpr
    rw [linPrice,hc]
    ring
