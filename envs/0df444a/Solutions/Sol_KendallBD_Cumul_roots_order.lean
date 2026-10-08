-- Prove2me | solution 1 for KendallBD.Cumul.roots_order
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:17:10.612007+00:00
-- url     : https://prove2.me/submissions/abdc6c78-3026-47fc-9dca-6209d10cc84d

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting
open Filter Topology KendallBD.Cumul

theorem solution (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    ∀ w ∈ Set.Ioo (0:ℝ) 1,
      0 < disc lam0 mu0 w ∧
      lam0 * w * alpha lam0 mu0 w ^ 2 - (lam0 + mu0) * alpha lam0 mu0 w + mu0 = 0 ∧
      lam0 * w * beta lam0 mu0 w ^ 2 - (lam0 + mu0) * beta lam0 mu0 w + mu0 = 0 ∧
      0 < alpha lam0 mu0 w ∧ alpha lam0 mu0 w < 1 ∧ 1 < beta lam0 mu0 w := by
  intro w hw
  have hmu : 0 < mu0 := lt_of_lt_of_le hlam hle
  have hp : 0 < lam0 * mu0 * (1 - w) := mul_pos (mul_pos hlam hmu) (by linarith [hw.2])
  have hd : 0 < disc lam0 mu0 w := by
    unfold disc
    nlinarith [sq_nonneg (lam0 - mu0)]
  have hs := Real.sq_sqrt hd.le
  change Real.sqrt (disc lam0 mu0 w) ^ 2 = (lam0 + mu0) ^ 2 - 4 * lam0 * mu0 * w at hs
  have hs0 := Real.sqrt_nonneg (disc lam0 mu0 w)
  have hden : 0 < 2 * lam0 * w := mul_pos (by linarith) hw.1
  have hden0 := ne_of_gt hden
  have hsum : Real.sqrt (disc lam0 mu0 w) < lam0 + mu0 := by
    have hprod : 0 < lam0 * mu0 * w := mul_pos (mul_pos hlam hmu) hw.1
    nlinarith
  have ha0 : 0 < alpha lam0 mu0 w := by
    unfold alpha
    exact div_pos (sub_pos.mpr hsum) hden
  have hb1 : 1 < beta lam0 mu0 w := by
    unfold beta
    apply (lt_div_iff₀ hden).mpr
    have hlw : lam0 * w < lam0 := by nlinarith [hw.2]
    nlinarith
  have haRoot : lam0 * w * alpha lam0 mu0 w ^ 2 -
      (lam0 + mu0) * alpha lam0 mu0 w + mu0 = 0 := by
    unfold alpha
    field_simp [ne_of_gt hlam, ne_of_gt hw.1]
    nlinarith
  have hbRoot : lam0 * w * beta lam0 mu0 w ^ 2 -
      (lam0 + mu0) * beta lam0 mu0 w + mu0 = 0 := by
    unfold beta
    field_simp [ne_of_gt hlam, ne_of_gt hw.1]
    nlinarith
  have ha1 : alpha lam0 mu0 w < 1 := by
    unfold alpha
    apply (div_lt_iff₀ hden).mpr
    have hdiff : lam0 + mu0 - 2 * lam0 * w ≥ 0 := by
      nlinarith [hw.2]
    nlinarith [sq_nonneg (Real.sqrt (disc lam0 mu0 w) - (lam0 + mu0 - 2 * lam0 * w)),
      mul_pos (mul_pos hlam hlam) (mul_pos hw.1 (sub_pos.mpr hw.2))]
  exact ⟨hd, haRoot, hbRoot, ha0, ha1, hb1⟩

#print axioms solution
