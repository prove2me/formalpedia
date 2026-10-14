-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.eventual_bounded_raw_packet_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T06:59:47.784633+00:00
-- url     : https://prove2.me/submissions/efec13f6-ee9d-4fe5-a6f6-0915b858f2c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_unrestricted_raw_packet_surjective
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_raw_packet_zero_of_mem_simultaneousJetIdeal_pow
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_weighted_representatives_of_jet_powers

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {nu : ℝ} (d : FixedData nu) (R S : ℝ)
    (e : Fin (d.m + 1) → ℕ)
    (hR : 0 < R) (hRS : R < S)
    (he : ∀ i, 0 < e i)
    (hcommon : ∀ i, S = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (hcapacity : 2 * R ^ (d.m + 1 : ℕ) > S ^ (d.m + 1 : ℕ)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Surjective
        (fun Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * R) =>
          rawPacketMap d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d))
            (((n + d.m : ℕ) : ℝ) * S)
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            Q.val) := by
  classical
  let w : Fin d.m → ℝ := MatrixArithmetic.logWeights (finiteDenominators d)
  let r : Fin d.m → ℂ :=
    MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)
  have hw : ∀ i, 0 < w i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log i.val]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le (i.val + 1))
  have hweights : ∀ i : Fin (d.m + 1),
      0 < InterpolationMatrix.rowWeights d.v0 d.base.theta w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [InterpolationMatrix.rowWeights] using d.v0_pos
    · simpa [InterpolationMatrix.rowWeights] using
        div_pos (hw j) d.base.theta_pos
  let T : Fin d.m → ℕ := fun i =>
    ⌈(w i / (d.base.theta : ℝ)) / (d.v0 : ℝ)⌉₊ + 1
  have hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta w i.succ <
      (T i : ℝ) * (d.v0 : ℝ) := by
    intro i
    change w i / (d.base.theta : ℝ) < (T i : ℝ) * (d.v0 : ℝ)
    apply (div_lt_iff₀ d.v0_pos).mp
    have hc := Nat.le_ceil ((w i / (d.base.theta : ℝ)) / (d.v0 : ℝ))
    dsimp only [T]
    push_cast
    linarith
  have hr : ∃ i, r i ≠ 0 := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    refine ⟨i, ?_⟩
    change 2 * Complex.I * (d.p i.val : ℂ) / (d.q i.val : ℂ) ≠ 0
    apply div_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
      · exact_mod_cast (d.approximations i.val).2.1
    · exact_mod_cast (show d.q i.val ≠ 0 by
        have := (d.approximations i.val).1
        omega)
  obtain ⟨A, hA, hAR, N0, hN0⟩ :=
    eventual_weighted_representatives_of_jet_powers d R S e T
      hR hRS he hcommon hcapacity hT
  have hgap : 0 < R - A := sub_pos.mpr hAR
  obtain ⟨M, hM⟩ := exists_nat_ge ((d.m : ℝ) * A / (R - A))
  have hpad : ∀ n : ℕ, M ≤ n →
      (((n + d.m : ℕ) : ℝ) * A) ≤ (n : ℝ) * R := by
    intro n hn
    have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hb : (d.m : ℝ) * A ≤ (n : ℝ) * (R - A) :=
      (div_le_iff₀ hgap).mp (hM.trans hMn)
    push_cast
    nlinarith
  refine ⟨max N0 M, ?_⟩
  intro n hn y
  have hn0 : N0 ≤ n + d.m := by omega
  have hnM : M ≤ n := by omega
  obtain ⟨P, hP⟩ :=
    unrestricted_raw_packet_surjective d.K d.v0 d.base.theta w
      (((n + d.m : ℕ) : ℝ) * S) r hr y
  obtain ⟨Q, hQ⟩ := hN0 (n + d.m) hn0 P
  let Q' : WeightedPolynomial d.w0 w ((n : ℝ) * R) :=
    ⟨Q.val, fun a ha => (Q.property a ha).trans (hpad n hnM)⟩
  have hz := raw_packet_zero_of_mem_simultaneousJetIdeal_pow
    d.K d.v0 d.base.theta w r T e S hweights he hcommon
    (fun i => (hT i).le) (n + d.m) (P - Q.val) hQ
  refine ⟨Q', ?_⟩
  funext rho
  have hzero :
      rawPacketMap d.K d.v0 d.base.theta w
          (((n + d.m : ℕ) : ℝ) * S) r P rho -
        rawPacketMap d.K d.v0 d.base.theta w
          (((n + d.m : ℕ) : ℝ) * S) r Q.val rho = 0 := by
    simpa only [rawPacketMap, map_sub] using congrFun hz rho
  change rawPacketMap d.K d.v0 d.base.theta w
    (((n + d.m : ℕ) : ℝ) * S) r Q.val rho = y rho
  exact (sub_eq_zero.mp hzero).symm.trans (congrFun hP rho)