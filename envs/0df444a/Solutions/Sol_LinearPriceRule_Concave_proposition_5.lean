-- Prove2me | solution 1 for LinearPriceRule.Concave.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:42:01.262777+00:00
-- url     : https://prove2.me/submissions/63ad6678-66f4-44c7-a898-5d9ed565ddfa

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

lemma ratios_of_price_lower (M : Market) (hM : M.Standing) {Q : ℝ}
    (hQ : IsOptQty M Q) (hlower : linPrice M ≤ M.PA Q) :
    (1 ≤ profit M Q / linProfit M ∧ profit M Q / linProfit M ≤ 2) ∧
    (1 ≤ M.PA Q / linPrice M ∧ M.PA Q / linPrice M ≤ 2) := by
  have hP := linPrice_pos M hM
  have hprofit := linProfit_pos M hM
  have hPm : M.PA Q ≤ M.Pm := by
    rw [← hM.PA_zero]
    exact hM.antitone ⟨le_rfl, hM.Qmax_pos.le⟩ hQ.1 hQ.1.1
  have hQD : Q ≤ demandAt M (linPrice M) :=
    le_csSup (demand_bddAbove M (linPrice M)) ⟨hQ.1, hlower⟩
  have hupper : profit M Q ≤ 2 * linProfit M := by
    calc
      profit M Q ≤ (M.Pm - M.c) * Q :=
        mul_le_mul_of_nonneg_right (sub_le_sub_right hPm M.c) hQ.1.1
      _ ≤ (M.Pm - M.c) * demandAt M (linPrice M) :=
        mul_le_mul_of_nonneg_left hQD (sub_nonneg.mpr hM.c_lt_Pm.le)
      _ = 2 * linProfit M := by unfold linProfit linPrice; ring
  refine ⟨⟨(le_div_iff₀ hprofit).2 ?_, (div_le_iff₀ hprofit).2 hupper⟩,
    ⟨(le_div_iff₀ hP).2 ?_, (div_le_iff₀ hP).2 ?_⟩⟩
  · simpa using linProfit_le_opt M hM hQ
  · simpa using hlower
  · dsimp [linPrice]
    linarith [hM.c_nonneg]

end LinearPriceRule.Concave.RootProof

namespace LinearPriceRule.Concave

theorem concave_price_lower (M : Market) (hM : M.Standing)
    (hconc : ConcaveOn ℝ (Set.Icc 0 M.Qmax) M.PA) (Q : ℝ) (hQ : IsOptQty M Q) :
    linPrice M ≤ M.PA Q := by
  by_contra h
  have hp : M.PA Q < (M.Pm + M.c) / 2 := by
    simpa only [linPrice] using lt_of_not_ge h
  have hQnonneg : 0 ≤ Q := hQ.1.1
  have hQpos : 0 < Q := by
    by_contra hpos
    have hzero : Q = 0 := by linarith
    rw [hzero, hM.PA_zero] at hp
    linarith [hM.c_lt_Pm]
  have hgap : 0 < M.Pm - M.PA Q := by linarith [hM.c_lt_Pm]
  have hmargin : 0 < M.Pm - M.c := sub_pos.mpr hM.c_lt_Pm
  let t : ℝ := (M.Pm - M.c) / (2 * (M.Pm - M.PA Q))
  have hden : 0 < 2 * (M.Pm - M.PA Q) := by positivity
  have htpos : 0 < t := div_pos hmargin hden
  have htlt : t < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hteq : t * (M.Pm - M.PA Q) = (M.Pm - M.c) / 2 := by
    dsimp [t]
    field_simp
  have htQ : t * Q ∈ Set.Icc 0 M.Qmax := by
    constructor
    · positivity
    · have hle : t * Q ≤ Q := by nlinarith
      exact hle.trans hQ.1.2
  have hzero : (0 : ℝ) ∈ Set.Icc 0 M.Qmax := ⟨le_rfl, hM.Qmax_pos.le⟩
  have hc := hconc.2 hzero hQ.1
    (show 0 ≤ 1 - t by linarith) htpos.le (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, hM.PA_zero] at hc
  have hopt := hQ.2 (t * Q) htQ
  have hbound : ((1 - t) * M.Pm + t * M.PA Q - M.c) * t ≤ M.PA Q - M.c := by
    refine le_of_mul_le_mul_right ?_ hQpos
    calc
      (((1 - t) * M.Pm + t * M.PA Q - M.c) * t) * Q =
          ((1 - t) * M.Pm + t * M.PA Q - M.c) * (t * Q) := by ring
      _ ≤ (M.PA (t * Q) - M.c) * (t * Q) :=
        mul_le_mul_of_nonneg_right (sub_le_sub_right hc M.c) htQ.1
      _ ≤ (M.PA Q - M.c) * Q := hopt
  have hgain : 0 < (1 - t) * (t * (M.Pm - M.PA Q) - (M.PA Q - M.c)) := by
    apply mul_pos (by linarith)
    rw [hteq]
    linarith
  nlinarith

end LinearPriceRule.Concave

open LinearPriceRule.Concave

theorem solution (M : Market) (hM : M.Standing)
    (hconc : ConcaveOn ℝ (Set.Icc 0 M.Qmax) M.PA) :
    (∃ Q, IsOptQty M Q) ∧ 0 < linProfit M ∧
    ∀ Q, IsOptQty M Q →
      (1 ≤ profit M Q / linProfit M ∧ profit M Q / linProfit M ≤ 2) ∧
      (1 ≤ M.PA Q / linPrice M ∧ M.PA Q / linPrice M ≤ 2) := by
  refine ⟨RootProof.exists_opt M hM, RootProof.linProfit_pos M hM, ?_⟩
  intro Q hQ
  exact RootProof.ratios_of_price_lower M hM hQ (concave_price_lower M hM hconc Q hQ)
