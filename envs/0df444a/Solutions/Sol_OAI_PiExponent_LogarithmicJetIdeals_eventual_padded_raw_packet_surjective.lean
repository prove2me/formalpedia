-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.eventual_padded_raw_packet_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T17:34:10.517292+00:00
-- url     : https://prove2.me/submissions/b175cb0a-34dd-448b-8064-6946c976431e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_eventual_fixed_twist_ideal_representatives
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_raw_packets_surjective
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_ideal_power_packet_vanishing

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

private theorem fixed_padding_bound (S R : ℝ) (hS : 0 < S) (b : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ,
      ((n + b : ℕ) : ℝ) * R ≤ ((⌊(n : ℝ) * R / S⌋₊ + B : ℕ) : ℝ) * S := by
  obtain ⟨B, hB⟩ := exists_nat_gt (((b : ℝ) * R + S) / S)
  have hB' := (div_lt_iff₀ hS).mp hB
  refine ⟨B, ?_⟩
  intro n
  have hfloor := Nat.lt_floor_add_one ((n : ℝ) * R / S)
  have hmul := mul_lt_mul_of_pos_right hfloor hS
  have hdiv : (n : ℝ) * R / S * S = (n : ℝ) * R := div_mul_cancel₀ _ hS.ne'
  push_cast
  nlinarith

private theorem floor_eventual_bound (S R : ℝ) (hS : 0 < S)
    (hR : 0 < R) (M : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      M ≤ ⌊(n : ℝ) * R / S⌋₊ ∧
      (⌊(n : ℝ) * R / S⌋₊ : ℝ) * S ≤ (n : ℝ) * R := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((M : ℝ) * S / R)
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hMR : (M : ℝ) * S ≤ (n : ℝ) * R :=
    (div_le_iff₀ hR).mp (hN.le.trans hn')
  have hnonneg : 0 ≤ (n : ℝ) * R / S := by positivity
  have hfloor := Nat.floor_le hnonneg
  have hdiv : (n : ℝ) * R / S * S = (n : ℝ) * R := div_mul_cancel₀ _ hS.ne'
  refine ⟨(Nat.le_floor_iff hnonneg).mpr ((le_div_iff₀ hS).mpr hMR), ?_⟩
  have := mul_le_mul_of_nonneg_right hfloor hS.le
  nlinarith

private theorem simplex_mono {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) {H H' : ℝ} (hHH' : H ≤ H') :
    strictWeightedSimplex w H ⊆ strictWeightedSimplex w H' := by
  classical
  intro a ha
  obtain ⟨ha₀, ha₁⟩ := Finset.mem_filter.mp ha
  obtain ⟨ha₂, ha₃⟩ := Finset.mem_filter.mp ha₀
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨?_, ha₃.trans hHH'⟩, ha₁.trans_le hHH'⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  have hai := Finset.mem_range.mp ((Fintype.mem_piFinset.mp ha₂) i)
  apply Finset.mem_range.mpr
  exact lt_of_lt_of_le hai (Nat.add_le_add_right
    (Nat.floor_mono ((div_le_div_iff_of_pos_right (hw i)).mpr hHH')) 1)

private theorem packet_vanishing_mono {m : ℕ} (K : ℕ) (v0 theta : ℝ)
    (w : Fin m → ℝ) (r : Fin m → ℂ) (hv0 : 0 < v0)
    (htheta : 0 < theta) (hw : ∀ i, 0 < w i) {H H' : ℝ}
    (hHH' : H ≤ H') (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : rawPacketMap K v0 theta w H' r P = 0) :
    rawPacketMap K v0 theta w H r P = 0 := by
  have hv : ∀ i, 0 < InterpolationMatrix.rowWeights v0 theta w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) htheta) i
  funext rho
  let rho' : InterpolationMatrix.Row K v0 theta w H' :=
    ⟨rho.1, ⟨rho.2.val, simplex_mono _ hv hHH' rho.2.property⟩⟩
  exact congrFun hP rho'

private theorem fixed_centers_injective {nu : ℝ} (d : FixedData nu) :
    Function.Injective (fun j : Fin d.K => fun i : Fin d.m => (j.val : ℂ) *
      MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i) := by
  let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
  have hp : (d.p i.val : ℂ) ≠ 0 := by exact_mod_cast (d.approximations i.val).2.1
  have hq : (d.q i.val : ℂ) ≠ 0 := by
    have h := (d.approximations i.val).1
    exact_mod_cast (show d.q i.val ≠ 0 by omega)
  have hr : MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  intro j k h
  have hjk := mul_right_cancel₀ hr (congrFun h i)
  apply Fin.ext
  exact_mod_cast hjk

theorem solution
    {nu : ℝ} (d : FixedData nu) (R : ℚ) (hR : 0 < R) (b : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Surjective
        (fun Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)) =>
          rawPacketMap d.K d.v0 d.base.theta
            (MatrixArithmetic.logWeights (finiteDenominators d))
            (((n + b : ℕ) : ℝ) * (R : ℝ))
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            Q.val) := by
  classical
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hw : ∀ i, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log]
    exact zero_lt_one.trans_le (d.x_one_le _)
  obtain ⟨S, hS, T, e, he, hscale, hT, hrep⟩ :=
    eventual_fixed_twist_ideal_representatives d
  obtain ⟨B, hB⟩ := fixed_padding_bound S R hS b
  obtain ⟨M, hM⟩ := hrep B
  obtain ⟨N, hN⟩ := floor_eventual_bound S R hS hR' M
  refine ⟨N, ?_⟩
  intro n hn y
  obtain ⟨hk, hcol⟩ := hN n hn
  have hrow := hB n
  let k : ℕ := ⌊(n : ℝ) * R / S⌋₊
  obtain ⟨P, hP⟩ := raw_packets_surjective d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) (((n + b : ℕ) : ℝ) * R)
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    d.v0_pos d.base.theta_pos hw (fixed_centers_injective d) y
  obtain ⟨Q, hQ⟩ := hM k hk P
  have hvan := ideal_power_packet_vanishing d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    S T e d.v0_pos d.base.theta_pos hw hS hscale hT (k + B) (P - Q.val) hQ
  have hsmall := packet_vanishing_mono d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d))
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    d.v0_pos d.base.theta_pos hw hrow (P - Q.val) hvan
  refine ⟨⟨Q.val, fun a ha => (Q.property a ha).trans hcol⟩, ?_⟩
  funext rho
  have hz := congrFun hsmall rho
  have hy := congrFun hP rho
  simp only [rawPacketMap, map_sub, Pi.zero_apply] at hz
  change MvPowerSeries.coeff _ (formalJet _ Q.val) = y rho
  rw [← sub_eq_zero.mp hz]
  exact hy
