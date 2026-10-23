-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.formal_packet_eq_truncated_packet_of_row_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T05:57:51.639541+00:00
-- url     : https://prove2.me/submissions/4224bb89-6d9f-426e-b0f2-ecef231fc0ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_arbitrarily_large_nonzero_fixed_minor
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_arithmetic_lower_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventual_fixed_minor_analytic_upper_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collision_rate_eventually_exceeds_two
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

noncomputable section

-- These numerical consequences use no interpolation or approximation theorem.
theorem packet_parameters_two_lt {nu : Real} (b : Parameters nu) : 2 < nu := by
  have hA : 0 < (b.A : Real) := lt_trans b.theta_pos b.theta_lt_A
  have hB : 0 < (b.B : Real) := lt_trans hA b.A_lt_B
  have hC : 0 < (b.C : Real) := lt_trans zero_lt_one b.one_lt_C
  have hBC : (b.B : Real) * (b.C : Real) < 1 :=
    (lt_div_iff₀ hC).mp b.B_lt_inv_C
  have hBsq : (b.B : Real) * (b.B : Real) < (b.theta : Real) := by
    calc
      (b.B : Real) * (b.B : Real) <
          ((b.C : Real) * (b.theta : Real)) * (b.B : Real) :=
        mul_lt_mul_of_pos_right b.B_lt_C_theta hB
      _ = (b.theta : Real) * ((b.B : Real) * (b.C : Real)) := by ring
      _ < (b.theta : Real) * 1 := mul_lt_mul_of_pos_left hBC b.theta_pos
      _ = (b.theta : Real) := mul_one _
  by_contra hnu
  have hnu' : nu ≤ 2 := le_of_not_gt hnu
  have hprod : nu * ((b.A : Real) - (b.theta : Real)) ≤
      2 * ((b.A : Real) - (b.theta : Real)) :=
    mul_le_mul_of_nonneg_right hnu' (sub_nonneg.mpr b.theta_lt_A.le)
  nlinarith [b.approximation_gap, b.A_lt_B, sq_nonneg ((b.B : Real) - 1)]

theorem packet_total_error_lt {nu : Real} (d : FixedData nu) :
    d.arithmeticError + d.analyticError < d.epsilon := by
  calc
    d.arithmeticError + d.analyticError =
        nu / d.F0 +
          ((Arithmetic.lcmConstant * d.F0 * (d.m : Real) + 2 * Real.log 2) /
              (d.v0 : Real) + 100 * (d.K : Real) / (d.w0 : Real)) +
          (Arithmetic.lcmConstant * (∑ i : Fin d.m, 1 / d.x (i.val + 1)) +
            weightErrorCoefficient nu d.base.theta d.K / d.wstar) := by
      dsimp [AdmissibleParameters.arithmeticError,
        AdmissibleParameters.analyticError, AdmissibleParameters.translationError,
        AdmissibleParameters.holomorphicError, weightErrorCoefficient]
      ring
    _ < d.epsilon / 3 + d.epsilon / 3 + d.epsilon / 3 :=
      add_lt_add (add_lt_add d.initial_margin d.dimension_margin) d.weight_margin
    _ = d.epsilon := by ring

theorem packet_mean_bounds {nu : Real} (d : FixedData nu) (H : Real)
    (hH : 0 < H) (hN : 0 < actualRowCount d H) :
    0 ≤ actualMean d H ∧ actualMean d H ≤ (d.base.theta : Real) := by
  classical
  let w := MatrixArithmetic.logWeights (finiteDenominators d)
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact Nat.cast_nonneg _
  have hsnonneg : ∀ rho : Row d H,
      0 ≤ ∑ i : Fin d.m, (rho.2.val i.succ : Real) * w i := by
    intro rho
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hw i))
  have hsupper : ∀ rho : Row d H,
      (∑ i : Fin d.m, (rho.2.val i.succ : Real) * w i) ≤
        (d.base.theta : Real) * H := by
    intro rho
    have hrow := (Finset.mem_filter.mp rho.2.property).2
    have hrow'' : (d.v0 : Real) * (rho.2.val 0 : Real) +
        (∑ i : Fin d.m, (w i / (d.base.theta : Real)) *
          (rho.2.val i.succ : Real)) < H := by
      simpa only [Fin.sum_univ_succ, InterpolationMatrix.rowWeights,
        Fin.cases_zero, Fin.cases_succ] using hrow
    have hsumdiv :
        (∑ i : Fin d.m, (w i / (d.base.theta : Real)) *
          (rho.2.val i.succ : Real)) =
          (∑ i : Fin d.m, (rho.2.val i.succ : Real) * w i) /
            (d.base.theta : Real) := by
      calc
        (∑ i : Fin d.m, (w i / (d.base.theta : Real)) *
            (rho.2.val i.succ : Real)) =
            ∑ i : Fin d.m, ((rho.2.val i.succ : Real) * w i) *
              (d.base.theta : Real)⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i : Fin d.m, (rho.2.val i.succ : Real) * w i) *
              (d.base.theta : Real)⁻¹ := by rw [← Finset.sum_mul]
        _ = (∑ i : Fin d.m, (rho.2.val i.succ : Real) * w i) /
              (d.base.theta : Real) := by rw [div_eq_mul_inv]
    have hrow' : (d.v0 : Real) * (rho.2.val 0 : Real) +
        (∑ i : Fin d.m, (rho.2.val i.succ : Real) * w i) /
          (d.base.theta : Real) < H := by
      simpa only [hsumdiv] using hrow''
    have hv : 0 ≤ (d.v0 : Real) * (rho.2.val 0 : Real) :=
      mul_nonneg d.v0_pos.le (Nat.cast_nonneg _)
    have hdiv : (∑ i : Fin d.m, (rho.2.val i.succ : Real) * w i) /
        (d.base.theta : Real) < H :=
      lt_of_le_of_lt (le_add_of_nonneg_left hv) hrow'
    have h := (div_lt_iff₀ d.base.theta_pos).mp hdiv
    simpa only [mul_comm] using h.le
  have hden : 0 < (actualRowCount d H : Real) * H :=
    mul_pos (Nat.cast_pos.mpr hN) hH
  have hsum0 : 0 ≤
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H := by
    exact Finset.sum_nonneg (fun rho _ => hsnonneg rho)
  have hsum : MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H ≤
      (actualRowCount d H : Real) * ((d.base.theta : Real) * H) := by
    calc
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta (finiteDenominators d) H ≤
          ∑ _rho : Row d H, (d.base.theta : Real) * H :=
        Finset.sum_le_sum (fun rho _ => hsupper rho)
      _ = (actualRowCount d H : Real) * ((d.base.theta : Real) * H) := by
        simp [actualRowCount, nsmul_eq_mul]
  constructor
  · exact div_nonneg hsum0 hden.le
  · apply (div_le_iff₀ hden).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hsum

-- The four proposed children imply nonexistence of admissible fixed data.
-- This is a global determinant argument, independent of formal/truncated
-- coefficient comparison.
theorem packet_fixed_data_false (nu : Real) (d : FixedData nu) : False := by
  classical
  have hnu : 2 < nu := packet_parameters_two_lt d.base
  have herr := packet_total_error_lt d
  let delta : Real := (d.epsilon - (d.arithmeticError + d.analyticError)) / 4
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have herr' : d.arithmeticError + d.analyticError + 2 * delta < d.epsilon := by
    dsimp [delta]
    linarith
  obtain ⟨LA, hLA⟩ := Filter.eventually_atTop.mp
    (eventual_fixed_minor_arithmetic_lower_bound nu d delta hdelta)
  obtain ⟨LB, hLB⟩ := Filter.eventually_atTop.mp
    (eventual_fixed_minor_analytic_upper_bound nu d delta hdelta)
  obtain ⟨LC, hLC⟩ := Filter.eventually_atTop.mp
    (collision_rate_eventually_exceeds_two nu d)
  obtain ⟨H, hLH, hH, hN, selection, hdet⟩ :=
    arbitrarily_large_nonzero_fixed_minor nu d (max LA (max LB LC))
  have hLAH : LA ≤ H := (le_max_left LA (max LB LC)).trans hLH
  have hLBH : LB ≤ H :=
    (le_trans (le_max_left LB LC) (le_max_right LA (max LB LC))).trans hLH
  have hLCH : LC ≤ H :=
    (le_trans (le_max_right LB LC) (le_max_right LA (max LB LC))).trans hLH
  have hlower := hLA H hLAH hH hN selection hdet
  have hupper := hLB H hLBH hH hN selection hdet
  have hcollision := hLC H hLCH
  obtain ⟨hmean0, hmeanθ⟩ := packet_mean_bounds d H hH hN
  have hscale : 0 ≤ (nu - 1) * ((d.base.theta : Real) - actualMean d H) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hmeanθ)
  have hgap : d.arithmeticError + d.analyticError + 2 * delta <
      nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
        (1 - actualMean d H) := by
    nlinarith [d.epsilon_lt_gap]
  rcases le_total (-collisionRate d H)
      (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)) with hc | hc
  · rw [max_eq_right hc] at hupper
    linarith
  · rw [max_eq_left hc] at hupper
    linarith [d.epsilon_le_half]

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real)
    (T : Fin d.m → Nat)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) H) :
    packetMap d H P =
      truncatedPolynomialPacket d.K d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) H
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d)) T P.val := by
  exact False.elim (packet_fixed_data_false nu d)
