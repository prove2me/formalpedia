-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.eventual_slack_bounded_representatives
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T17:59:09.697987+00:00
-- url     : https://prove2.me/submissions/dc8d3b30-3090-4ab9-9b78-8d59d1fa8073
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_strict_scale_padded_packet_interpolation
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_padded_packet_kernel_in_simultaneous_power

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

lemma solution_row_weights_pos {nu : ℝ} (d : FixedData nu) :
    ∀ i, 0 < InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact d.v0_pos
  · change 0 < MatrixArithmetic.logWeights (finiteDenominators d) j / (d.base.theta : ℝ)
    apply div_pos _ d.base.theta_pos
    have h : 1 ≤ MatrixArithmetic.logWeights (finiteDenominators d) j := by
      simpa [MatrixArithmetic.logWeights, finiteDenominators, d.x_log] using
        d.x_one_le (j.val + 1)
    linarith

lemma solution_centers_injective {nu : ℝ} (d : FixedData nu) :
    Function.Injective (fun j : Fin d.K => fun i : Fin d.m =>
      (j.val : ℂ) * MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i) := by
  let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
  have hp : (finiteNumerators d i : ℂ) ≠ 0 := by
    exact_mod_cast (d.approximations i.val).2.1
  have hq : (finiteDenominators d i : ℂ) ≠ 0 := by
    have : finiteDenominators d i ≠ 0 := by
      have := (d.approximations i.val).1
      change d.q i.val ≠ 0
      omega
    exact_mod_cast this
  have hr : MatrixArithmetic.rationalCenters
      (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  intro j k hjk
  have h := mul_right_cancel₀ hr (congrFun hjk i)
  apply Fin.ext
  exact_mod_cast h

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∃ R S : ℝ, 0 < R ∧ R < S ∧
      ∃ T : Fin d.m → ℕ, ∃ e : Fin (d.m + 1) → ℕ,
        (∀ i, 0 < e i) ∧
        (∀ i, S ≤ (e i : ℝ) *
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i) ∧
        (∀ i : Fin d.m,
          InterpolationMatrix.rowWeights d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
              (T i : ℝ) * (d.v0 : ℝ)) ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
            ∃ Q : WeightedPolynomial d.w0
                (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * R),
              P - Q.val ∈ (simultaneousJetIdeal d.K
                (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
                T e) ^ n := by
  classical
  obtain ⟨R, S, hR, hRS, e, he, hscale, N, hsurj⟩ :=
    strict_scale_padded_packet_interpolation d
  let T : Fin d.m → ℕ := fun i => ⌈
    InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ / (d.v0 : ℝ)⌉₊
  have hT : ∀ i : Fin d.m,
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
          (T i : ℝ) * (d.v0 : ℝ) := by
    intro i
    apply (div_le_iff₀ d.v0_pos).mp
    exact Nat.le_ceil _
  refine ⟨R, S, hR, hRS, T, e, he, (fun i => (hscale i).le), hT, N, ?_⟩
  intro n hn P
  obtain ⟨Q, hQ⟩ := hsurj n hn
    (rawPacketMap d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))
      (((n + d.m : ℕ) : ℝ) * S)
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) P)
  refine ⟨Q, ?_⟩
  apply padded_packet_kernel_in_simultaneous_power d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) S
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    T e (lt_trans hR hRS) (solution_row_weights_pos d) he
    (fun i => (hscale i).symm.le) hT (solution_centers_injective d) n
  ext rho
  have h := congrFun hQ rho
  simpa [rawPacketMap, map_sub] using sub_eq_zero.mpr h.symm
