-- Prove2me | solution 1 for LinearPriceRule.Concave.theorem_1_convex
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:42:06.212084+00:00
-- url     : https://prove2.me/submissions/476333f2-2e8a-4bed-8ad4-da06ccd17f64

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

namespace LinearPriceRule.Concave.RootProof

lemma exists_opt (M : Market) (hM : M.Standing) : ∃ Q, IsOptQty M Q := by
  have hc : ContinuousOn (profit M) (Set.Icc 0 M.Qmax) :=
    (hM.continuous.sub continuousOn_const).mul continuousOn_id
  obtain ⟨Q, hQ, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hM.Qmax_pos.le) hc
  exact ⟨Q, hQ, hmax⟩

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

lemma linPrice_pos (M : Market) (hM : M.Standing) : 0 < linPrice M := by
  dsimp [linPrice]
  linarith [hM.c_nonneg, hM.c_lt_Pm]

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

theorem solution (M : Market) (hM : M.Standing)
    (hconv : ConvexOn ℝ (Set.Icc 0 M.Qmax) M.PA) (Q : ℝ) (hQ : IsOptQty M Q)
    (hint : Q < M.Qmax) : M.PA Q ≤ linPrice M := by
  have hprofit := RootProof.profit_opt_pos M hM hQ
  have hQpos : 0 < Q := by
    by_contra h
    have hzero : Q = 0 := by linarith [hQ.1.1]
    simp [profit, hzero] at hprofit
  have hpmax : M.PA Q ≤ M.Pm := by
    rw [← hM.PA_zero]
    exact hM.antitone ⟨le_rfl, hM.Qmax_pos.le⟩ hQ.1 hQ.1.1
  by_contra h
  have hp : (M.Pm + M.c) / 2 < M.PA Q := by
    simpa only [linPrice] using lt_of_not_ge h
  have hgap : 0 < 2 * M.PA Q - M.Pm - M.c := by linarith
  have hden : 0 < 2 * (M.Pm - M.PA Q + 1) := by linarith
  let ε : ℝ := min ((M.Qmax - Q) / (2 * Q))
    ((2 * M.PA Q - M.Pm - M.c) / (2 * (M.Pm - M.PA Q + 1)))
  have hεpos : 0 < ε := lt_min
    (div_pos (sub_pos.mpr hint) (by positivity)) (div_pos hgap hden)
  have hεQ : ε * (2 * Q) ≤ M.Qmax - Q :=
    (le_div_iff₀ (by positivity : 0 < 2 * Q)).mp (min_le_left _ _)
  have hεgap : ε * (2 * (M.Pm - M.PA Q + 1)) ≤ 2 * M.PA Q - M.Pm - M.c :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  let t : ℝ := 1 + ε
  have ht : 1 < t := by dsimp [t]; linarith
  have htpos : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hqI : t * Q ∈ Set.Icc 0 M.Qmax := by
    constructor
    · positivity
    · dsimp [t]
      nlinarith
  have hinv : 0 < 1 / t := div_pos (by norm_num) htpos
  have hinvle : 1 / t ≤ 1 := (div_le_one htpos).mpr ht.le
  have hc := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 M.Qmax from ⟨le_rfl, hM.Qmax_pos.le⟩)
    hqI (show 0 ≤ 1 - 1 / t by linarith) hinv.le (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, hM.PA_zero] at hc
  have hfrac : (1 / t) * (t * Q) = Q := by field_simp
  rw [hfrac] at hc
  have hm := mul_le_mul_of_nonneg_left hc htpos.le
  have hright : t * ((1 - 1 / t) * M.Pm + (1 / t) * M.PA (t * Q)) =
      (t - 1) * M.Pm + M.PA (t * Q) := by field_simp
  rw [hright] at hm
  have hsecant : (1 - t) * M.Pm + t * M.PA Q ≤ M.PA (t * Q) := by linarith
  have hopt := hQ.2 (t * Q) hqI
  have hbound : ((1 - t) * M.Pm + t * M.PA Q - M.c) * t ≤ M.PA Q - M.c := by
    refine le_of_mul_le_mul_right ?_ hQpos
    calc
      (((1 - t) * M.Pm + t * M.PA Q - M.c) * t) * Q =
          ((1 - t) * M.Pm + t * M.PA Q - M.c) * (t * Q) := by ring
      _ ≤ (M.PA (t * Q) - M.c) * (t * Q) :=
        mul_le_mul_of_nonneg_right (sub_le_sub_right hsecant M.c) hqI.1
      _ ≤ (M.PA Q - M.c) * Q := hopt
  have hmargin : 0 < M.PA Q - M.c - t * (M.Pm - M.PA Q) := by
    dsimp [t]
    nlinarith
  have hgain : 0 < (t - 1) * (M.PA Q - M.c - t * (M.Pm - M.PA Q)) :=
    mul_pos (sub_pos.mpr ht) hmargin
  nlinarith
