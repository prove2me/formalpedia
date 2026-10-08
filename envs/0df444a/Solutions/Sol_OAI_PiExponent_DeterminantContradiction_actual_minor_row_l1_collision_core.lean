-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_collision_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T04:48:53.939891+00:00
-- url     : https://prove2.me/submissions/07ea1029-0624-4d1b-b8bb-b8fb2e2f148e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_row_l1_low_index_exp_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_actualRowCount_normalized
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Field

open Filter Topology
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

private theorem log_div_of_normalized_pow {f : ℝ → ℝ} {n : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ n) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H : ℝ => Real.log (f H) / H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log (f H / H ^ n)) atTop (𝓝 (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hf
  have hslow : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h := (hlog.div_atTop tendsto_id).add (hslow.const_mul (n : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_ne_nhds hL.ne')] with H hH hn
  have hfne : f H ≠ 0 := by
    intro hz
    apply hn
    simp [hz]
  rw [Real.log_div hfne (pow_ne_zero _ hH.ne'), Real.log_pow]
  simp only [id_eq]
  ring

private theorem envelope_normalized (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => translationEnvelope m v H / H ^ (2 * m + 1))
      atTop (𝓝 (1 / v)) := by
  have hsmall : Tendsto (fun H : ℝ => 1 / H) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have h1 : Tendsto (fun H : ℝ => (H + 1) / H) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
    field_simp
  have h2 : Tendsto (fun H : ℝ => (H / v + 1) / H) atTop (𝓝 (1 / v)) := by
    have ht := (tendsto_const_nhds (x := (1 / v : ℝ))).add hsmall
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
    field_simp
  have h := (h1.pow (2 * m)).mul h2
  simp only [one_pow, one_mul] at h
  convert h using 1
  funext H
  simp only [translationEnvelope, div_pow, div_mul_div_comm, pow_succ]

private theorem remainder_tendsto {nu : ℝ} (d : FixedData nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  have hw : ∀ i : Fin d.m, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log i.val]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  have hlead : 0 < (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, MatrixArithmetic.logWeights (finiteDenominators d) i) := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos)
        (pow_pos d.base.theta_pos _)
    · exact mul_pos (mul_pos (by positivity) d.v0_pos)
        (Finset.prod_pos fun i _ => hw i)
  have hr := log_div_of_normalized_pow (tendsto_actualRowCount_normalized d) hlead
  have hc := tendsto_id.const_div_atTop
    (Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)))
  have hq := log_div_of_normalized_pow (envelope_normalized d.m d.v0_pos)
    (div_pos zero_lt_one d.v0_pos)
  convert (hr.add hc).add hq using 1
  · funext H
    unfold analyticRemainder
    simp only [id_eq]
    ring
  · norm_num

private theorem rowCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H := by
  classical
  let r : Row d H := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩,
    ⟨fun _ => 0, by simp [strictWeightedSimplex, realWeightedSimplex, hH, hH.le]⟩⟩
  have : Nonempty (Row d H) := ⟨r⟩
  exact Fintype.card_pos

private theorem mean_le_theta {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    actualMean d H ≤ (d.base.theta : ℝ) := by
  classical
  have hM : 0 < (actualRowCount d H : ℝ) := by exact_mod_cast rowCount_pos d hH
  unfold actualMean MatrixArithmetic.meanRowWeight
  apply (div_le_iff₀ (mul_pos hM hH)).mpr
  calc
    MatrixArithmetic.rowWeightedSum _ _ _ _ _ ≤
        ∑ _r : Row d H, H * (d.base.theta : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      have hb := (Finset.mem_filter.mp r.2.2).2
      change ∑ i : Fin (d.m + 1),
        InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d)) i * (r.2.1 i : ℝ) < H at hb
      rw [Fin.sum_univ_succ] at hb
      simp only [InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ,
        div_mul_eq_mul_div, ← Finset.sum_div] at hb
      have h0 : 0 ≤ (d.v0 : ℝ) * (r.2.1 0 : ℝ) :=
        mul_nonneg d.v0_pos.le (Nat.cast_nonneg _)
      have hh : (∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) /
          (d.base.theta : ℝ) ≤ H := by linarith
      have hm := (div_le_iff₀ d.base.theta_pos).mp hh
      simpa only [mul_comm] using hm
    _ = (d.base.theta : ℝ) *
        ((Fintype.card (Row d H) : ℝ) * H) := by simp; ring

private theorem analytic_small {nu : ℝ} (d : FixedData nu) :
    d.analyticError < nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) := by
  have hsum : d.arithmeticError + d.analyticError <
      nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
        (1 - d.base.theta) := by
    have he : d.arithmeticError + d.analyticError =
        nu / d.F0 +
        ((Arithmetic.lcmConstant * d.F0 * (d.m : ℝ) + 2 * Real.log 2) / (d.v0 : ℝ) +
          100 * (d.K : ℝ) / (d.w0 : ℝ)) +
        (Arithmetic.lcmConstant * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
          weightErrorCoefficient nu d.base.theta d.K / d.wstar) := by
      unfold AdmissibleParameters.arithmeticError AdmissibleParameters.analyticError
        AdmissibleParameters.translationError AdmissibleParameters.holomorphicError
        weightErrorCoefficient
      ring
    rw [he]
    linarith [d.initial_margin, d.dimension_margin, d.weight_margin, d.epsilon_lt_gap]
  have har : 0 ≤ d.arithmeticError := by
    unfold AdmissibleParameters.arithmeticError Arithmetic.lcmConstant
    have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hF := d.F0_pos
    have hv := d.v0_pos
    have hw := d.wstar_pos
    have htheta := d.base.theta_pos
    have hx : 0 ≤ ∑ i : Fin d.m, 1 / d.x (i.val + 1) := by
      apply Finset.sum_nonneg
      intro i _
      exact one_div_nonneg.mpr ((zero_le_one : (0 : ℝ) ≤ 1).trans (d.x_one_le _))
    positivity
  have ht : (d.base.theta : ℝ) < 1 :=
    d.base.theta_lt_A.trans (d.base.A_lt_B.trans d.base.B_lt_one)
  linarith

-- The only open dependency is the existing low-index row estimate.
-- Its constant-row specialization rules out the supplied fixed data.
theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (selection : Row d H -> Column d H)
    (rowIdx : Row d H) :
    Finset.sum Finset.univ (fun colIdx : Row d H =>
      norm ((actualMinor d H selection) rowIdx colIdx)) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -collisionRate d H)) := by
  classical
  exfalso
  have hsmall : ∀ᶠ t : ℝ in atTop,
      d.analyticError + analyticRemainder d t <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) := by
    have ht := (tendsto_const_nhds (x := d.analyticError)).add (remainder_tendsto d)
    exact ht.eventually (Iio_mem_nhds (by simpa only [add_zero] using analytic_small d))
  obtain ⟨t, ht, ht0⟩ := (hsmall.and (eventually_gt_atTop (0 : ℝ))).exists
  let r : Row d t := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩,
    ⟨fun _ => 0, by simp [strictWeightedSimplex, realWeightedSimplex, ht0, ht0.le]⟩⟩
  let c : Column d t :=
    ⟨fun _ => 0, by simp [realWeightedSimplex, ht0.le]⟩
  have hentry : ∀ k : Row d t, actualMinor d t (fun _ => c) r k = 1 := by
    intro k
    have hz : Finsupp.equivFunOnFinite.symm (fun _ : Fin d.m => (0 : ℕ)) = 0 := by
      ext i
      simp
    simp [actualMinor, MatrixArithmetic.selectedMinor, Matrix.submatrix,
      InterpolationMatrix.truncatedLogMatrix, InterpolationMatrix.matrix,
      InterpolationMatrix.entry, InterpolationMatrix.monomialImage,
      InterpolationMatrix.exponentVector, r, c, hz]
  have hb := actual_minor_row_l1_low_index_exp_bound d hnu ht0 (fun _ => c) r
  simp only [hentry, norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hb
  have hneg : d.analyticError + analyticRemainder d t +
      -nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d t) < 0 := by
    have hh := mul_le_mul_of_nonneg_left (mean_le_theta d ht0) hnu
    nlinarith
  have hexp : Real.exp (t * (d.analyticError + analyticRemainder d t +
      -nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d t))) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg ht0 hneg)
  have hcard : (1 : ℝ) ≤ Fintype.card (Row d t) := by
    exact_mod_cast rowCount_pos d ht0
  linarith
