-- Prove2me | solution 1 for LinearPriceRule.Concave.demand_antitone
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:42:07.970713+00:00
-- url     : https://prove2.me/submissions/2a935262-af62-4f78-8825-7c0932dd17ca

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

set_option autoImplicit false

namespace LinearPriceRule.Concave.RootProof

lemma demand_bddAbove (M : Market) (p : ℝ) :
    BddAbove {Q : ℝ | Q ∈ Set.Icc 0 M.Qmax ∧ p ≤ M.PA Q} :=
  ⟨M.Qmax, fun _ hQ => hQ.1.2⟩

lemma demand_feasible (M : Market) (hM : M.Standing) {p : ℝ} (hp : p ≤ M.Pm) :
    demandAt M p ∈ Set.Icc 0 M.Qmax ∧ p ≤ M.PA (demandAt M p) := by
  have hclosed : IsClosed {Q : ℝ | Q ∈ Set.Icc 0 M.Qmax ∧ p ≤ M.PA Q} :=
    isClosed_Icc.isClosed_le continuousOn_const hM.continuous
  have hc : IsCompact {Q : ℝ | Q ∈ Set.Icc 0 M.Qmax ∧ p ≤ M.PA Q} :=
    isCompact_Icc.of_isClosed_subset hclosed (fun _ hQ => hQ.1)
  apply hc.sSup_mem
  exact ⟨0, ⟨le_rfl, hM.Qmax_pos.le⟩, hM.PA_zero ▸ hp⟩

lemma demand_pos (M : Market) (hM : M.Standing) {p : ℝ} (hp : p < M.Pm) :
    0 < demandAt M p := by
  have hcont := hM.continuous 0 ⟨le_rfl, hM.Qmax_pos.le⟩
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousWithinAt_iff.mp hcont
    (M.Pm - p) (sub_pos.mpr hp)
  let q : ℝ := min δ M.Qmax / 2
  have hqpos : 0 < q := div_pos (lt_min hδ hM.Qmax_pos) (by norm_num)
  have hqδ : q < δ := by
    dsimp [q]
    have := min_le_left δ M.Qmax
    linarith
  have hqmax : q ≤ M.Qmax := by
    dsimp [q]
    have := min_le_right δ M.Qmax
    linarith [hM.Qmax_pos]
  have hqI : q ∈ Set.Icc 0 M.Qmax := ⟨hqpos.le, hqmax⟩
  have hdist : dist q 0 < δ := by simpa [Real.dist_eq, abs_of_nonneg hqpos.le] using hqδ
  have hprice := hnear hqI hdist
  rw [Real.dist_eq, hM.PA_zero] at hprice
  have hqp : p ≤ M.PA q := by
    have := (abs_lt.mp hprice).1
    linarith
  exact hqpos.trans_le (le_csSup (demand_bddAbove M p) ⟨hqI, hqp⟩)

lemma linProfit_pos (M : Market) (hM : M.Standing) : 0 < linProfit M := by
  have hp : linPrice M < M.Pm := by
    dsimp [linPrice]
    linarith [hM.c_lt_Pm]
  have hm : 0 < linPrice M - M.c := by
    dsimp [linPrice]
    linarith [hM.c_lt_Pm]
  exact mul_pos hm (demand_pos M hM hp)


lemma linProfit_le_opt (M : Market) (hM : M.Standing) {Q : ℝ} (hQ : IsOptQty M Q) :
    linProfit M ≤ profit M Q := by
  have hp : linPrice M ≤ M.Pm := by
    dsimp [linPrice]
    linarith [hM.c_lt_Pm]
  have hd := demand_feasible M hM hp
  calc
    linProfit M ≤ profit M (demandAt M (linPrice M)) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hd.2 M.c) hd.1.1
    _ ≤ profit M Q := hQ.2 _ hd.1

lemma profit_opt_pos (M : Market) (hM : M.Standing) {Q : ℝ} (hQ : IsOptQty M Q) :
    0 < profit M Q := (linProfit_pos M hM).trans_le (linProfit_le_opt M hM hQ)

end LinearPriceRule.Concave.RootProof

open LinearPriceRule.Concave

theorem solution (M : Market) (hM : M.Standing) :
    AntitoneOn (demandAt M) (Set.Iic M.Pm) ∧
    ∀ Q, IsOptQty M Q → demandAt M (M.PA Q) = Q := by
  constructor
  · intro p hp p' hp' hpp'
    apply csSup_le
    · exact ⟨0, ⟨le_rfl, hM.Qmax_pos.le⟩, by simpa only [hM.PA_zero, Set.mem_Iic] using hp'⟩
    · intro q hq
      exact le_csSup (RootProof.demand_bddAbove M p) ⟨hq.1, hpp'.trans hq.2⟩
  · intro Q hQ
    have hprofit := RootProof.profit_opt_pos M hM hQ
    have hmargin : 0 < M.PA Q - M.c := by
      by_contra hm
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hm) hQ.1.1
      exact (not_le_of_gt hprofit) hnonpos
    apply le_antisymm
    · apply csSup_le
      · exact ⟨Q, hQ.1, le_rfl⟩
      · intro q hq
        have hcompare : (M.PA Q - M.c) * q ≤ (M.PA Q - M.c) * Q := by
          calc
            (M.PA Q - M.c) * q ≤ (M.PA q - M.c) * q :=
              mul_le_mul_of_nonneg_right (sub_le_sub_right hq.2 M.c) hq.1.1
            _ ≤ (M.PA Q - M.c) * Q := hQ.2 q hq.1
        exact (mul_le_mul_iff_right₀ hmargin).mp (by simpa only [mul_comm] using hcompare)
    · exact le_csSup (RootProof.demand_bddAbove M (M.PA Q)) ⟨hQ.1, le_rfl⟩
