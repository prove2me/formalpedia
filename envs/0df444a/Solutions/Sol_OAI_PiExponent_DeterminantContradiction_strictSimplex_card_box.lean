-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strictSimplex_card_box
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:24:22.01724+00:00
-- url     : https://prove2.me/submissions/cbad292d-6d69-45b2-a4e2-3e670fb95ab1

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (H : ℝ) (hH : 0 ≤ H) : (Fintype.card (↑(OAI.PiExponent.strictWeightedSimplex (OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta (OAI.PiExponent.MatrixArithmetic.logWeights (OAI.PiExponent.DeterminantContradiction.finiteDenominators d))) H) : Type) : ℝ) ≤ (H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m := by
  classical
  set w := OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
    (OAI.PiExponent.MatrixArithmetic.logWeights
      (OAI.PiExponent.DeterminantContradiction.finiteDenominators d)) with hw
  have hθ : (0 : ℝ) < d.base.theta := d.base.theta_pos
  have hθ1 : (d.base.theta : ℝ) < 1 := by
    have h1 := d.base.one_lt_C
    have h2 := d.base.C_theta_lt_one
    nlinarith
  have hv0 : (0 : ℝ) < d.v0 := d.v0_pos
  -- the weights of the later coordinates are at least one
  have hge : ∀ j : Fin d.m, 1 ≤ w j.succ := by
    intro j
    have hx := d.x_one_le (j.val + 1)
    rw [d.x_log] at hx
    have hw' : w j.succ = (⌈Real.log (d.q j.val)⌉₊ : ℝ) / d.base.theta := by
      simp [hw, OAI.PiExponent.InterpolationMatrix.rowWeights,
        OAI.PiExponent.MatrixArithmetic.logWeights,
        OAI.PiExponent.DeterminantContradiction.finiteDenominators]
    rw [hw', le_div_iff₀ hθ]
    nlinarith
  have hw0 : w 0 = d.v0 := by
    simp [hw, OAI.PiExponent.InterpolationMatrix.rowWeights]
  rw [Fintype.card_coe]
  have h1 : (OAI.PiExponent.strictWeightedSimplex w H).card ≤
      (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).card := by
    unfold OAI.PiExponent.strictWeightedSimplex OAI.PiExponent.realWeightedSimplex
    exact le_trans (Finset.card_filter_le _ _) (Finset.card_filter_le _ _)
  rw [Fintype.card_piFinset] at h1
  simp only [Finset.card_range] at h1
  have h2 : ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) ≤
      ∏ i, ((⌊H / w i⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast h1
  refine le_trans h2 ?_
  rw [Fin.prod_univ_succ]
  have hfirst : ((⌊H / w 0⌋₊ + 1 : ℕ) : ℝ) ≤ H / d.v0 + 1 := by
    rw [hw0]; push_cast
    have := Nat.floor_le (div_nonneg hH hv0.le)
    linarith
  have hrest : ∏ j : Fin d.m, ((⌊H / w j.succ⌋₊ + 1 : ℕ) : ℝ) ≤ (H + 1) ^ d.m := by
    have hc : (H + 1) ^ d.m = ∏ _j : Fin d.m, (H + 1) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc]
    apply Finset.prod_le_prod
    · intro j _; positivity
    · intro j _
      push_cast
      have hwj := hge j
      have hpos : 0 < w j.succ := by linarith
      have h3 := Nat.floor_le (div_nonneg hH hpos.le)
      have h4 : H / w j.succ ≤ H := div_le_self hH hwj
      linarith
  exact mul_le_mul hfirst hrest (by positivity) (by positivity)
