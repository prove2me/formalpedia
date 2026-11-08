-- Prove2me | solution 1 for HuangYin.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:14:19.447365+00:00
-- url     : https://prove2.me/submissions/f9f058c0-d8a8-4ddc-93c0-7cf1c5fbebcd

import Mathlib
import Definitions.Def_HuangYin_OptimalOffer
import Definitions.Def_HuangYin_vHL

namespace Aux_Q01_HuangYin_lemma_3
open HuangYin

theorem profit_eq (P : Params) (y1 y2 : ℝ) :
    opaqueProfit P (vHL P) P.vL y1 y2 =
      y1 * (vHL P - cost P y1) + (P.vL - cost P y2) := by
  have e0 : estimate false = 0 := by simp [estimate]
  have e1 : estimate true = 1 / 2 := by norm_num [estimate]
  have hv := P.hv
  have hnf : ¬ Buys P (vHL P) false := by
    intro h
    unfold Buys at h
    rw [e0] at h
    unfold vHL at h
    linarith
  have hpt : Buys P (vHL P) true := by
    unfold Buys vHL
    rw [e1]
    linarith
  have hlf : Buys P P.vL false := by
    unfold Buys
    rw [e0]
    linarith
  have hlt : Buys P P.vL true := by
    unfold Buys
    rw [e1]
    linarith
  unfold opaqueProfit demand
  rw [if_neg hnf, if_pos hpt, if_pos hlf, if_pos hlt]
  ring

end Aux_Q01_HuangYin_lemma_3

open HuangYin in
theorem solution (P : Params) (hcorr : P.cL ≤ vHL P) :
    ((vHL P - P.cL) / (P.cH - P.cL) < 2 →
      OptimalOffer P (vHL P) P.vL ((vHL P - P.cL) / (2 * (P.cH - P.cL))) 0) ∧
    (2 ≤ (vHL P - P.cL) / (P.cH - P.cL) →
      OptimalOffer P (vHL P) P.vL 1 0) := by
  have hΔ : 0 < P.cH - P.cL := sub_pos.mpr P.hc
  have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  constructor
  · intro hlt
    have hlt' : vHL P - P.cL < 2 * (P.cH - P.cL) := by
      rw [div_lt_iff₀ hΔ] at hlt
      linarith
    set x1 := (vHL P - P.cL) / (2 * (P.cH - P.cL)) with hx1def
    have hx1 : x1 * (2 * (P.cH - P.cL)) = vHL P - P.cL := by
      rw [hx1def]
      exact div_mul_cancel₀ _ (mul_pos two_pos hΔ).ne'
    have hx0 : 0 ≤ x1 := div_nonneg (by linarith) (mul_pos two_pos hΔ).le
    have hx1le : x1 ≤ 1 := by
      rw [hx1def, div_le_one (mul_pos two_pos hΔ)]
      linarith
    refine ⟨⟨hx0, hx1le⟩, hz, ?_⟩
    intro y1 hy1 y2 hy2
    rw [Aux_Q01_HuangYin_lemma_3.profit_eq, Aux_Q01_HuangYin_lemma_3.profit_eq]
    have hv : vHL P = P.cL + x1 * (2 * (P.cH - P.cL)) := by linarith
    clear_value x1
    rw [hv]
    unfold cost
    nlinarith [mul_nonneg hΔ.le (sq_nonneg (x1 - y1)), mul_nonneg hy2.1 hΔ.le]
  · intro hge
    have hge' : 2 * (P.cH - P.cL) ≤ vHL P - P.cL := by
      rw [le_div_iff₀ hΔ] at hge
      linarith
    refine ⟨⟨zero_le_one, le_refl _⟩, hz, ?_⟩
    intro y1 hy1 y2 hy2
    rw [Aux_Q01_HuangYin_lemma_3.profit_eq, Aux_Q01_HuangYin_lemma_3.profit_eq]
    have hA : 0 ≤ vHL P - P.cL - (P.cH - P.cL) * (1 + y1) := by
      nlinarith [mul_nonneg hΔ.le (sub_nonneg.mpr hy1.2)]
    unfold cost
    nlinarith [mul_nonneg (sub_nonneg.mpr hy1.2) hA, mul_nonneg hy2.1 hΔ.le]
