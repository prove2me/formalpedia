-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.eventual_weighted_representatives_of_scale
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T12:51:06.936903+00:00
-- url     : https://prove2.me/submissions/0f5a7718-dd87-4b05-b141-d92a441281b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_finiteColength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_subcritical_logarithmic_power_generation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_representatives_of_subcritical_power_generators
import Mathlib.Tactic.NormNum

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu)
    (R : ℚ) (T : Fin d.m → ℕ) (e : Fin (d.m + 1) → ℕ)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : ℝ) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : ℝ) = (e i : ℝ) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i) :
    ∀ᶠ n : ℕ in atTop,
      ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * (R : ℝ)),
          P - Q.val ∈ FormalInterpolation.logarithmicCentersIdeal
            (fun j : Fin d.K => fun i => (j.val : ℂ) *
              MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
            T e ^ n := by
  let r := MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)
  let c : Fin d.K → Fin d.m → ℂ := fun j i => (j.val : ℂ) * r i
  let I := FormalInterpolation.logarithmicCentersIdeal c T e
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hw : ∀ i : Fin d.m,
      0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    have hx := d.x_one_le (i.val + 1)
    rw [d.x_log i.val] at hx
    exact lt_of_lt_of_le zero_lt_one hx
  let i₀ : Fin d.m := ⟨0, d.m_pos⟩
  have hp : (d.p 0 : ℂ) ≠ 0 := by
    exact_mod_cast (d.approximations 0).2.1
  have hqnat : d.q 0 ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (d.approximations 0).1)
  have hq : (d.q 0 : ℂ) ≠ 0 := by exact_mod_cast hqnat
  have hr : r i₀ ≠ 0 := by
    change 2 * Complex.I * (d.p 0 : ℂ) / (d.q 0 : ℂ) ≠ 0
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
  have hdist : ∀ j k : Fin d.K, j ≠ k → c j ≠ c k := by
    intro j k hjk h
    have hmul : (j.val : ℂ) * r i₀ = (k.val : ℂ) * r i₀ := congrFun h i₀
    have hval : (j.val : ℂ) = (k.val : ℂ) := mul_right_cancel₀ hr hmul
    have hnat : j.val = k.val := by exact_mod_cast hval
    exact hjk (Fin.ext hnat)
  have hfinite :=
    FormalInterpolation.logarithmicCentersIdeal_finiteColength c T e he hdist
  obtain ⟨s, hs, D, hD, S, hspan, hdeg⟩ :=
    FormalInterpolation.fixedData_subcritical_logarithmic_power_generation
      nu hnu d R T e hR he hT hscale
  obtain ⟨N, hN⟩ :=
    FormalInterpolation.eventual_representatives_of_subcritical_power_generators
      d.w0 (MatrixArithmetic.logWeights (finiteDenominators d))
      d.w0_pos hw I hfinite (R : ℝ) hRreal s hs D hD S hspan hdeg
  exact Filter.eventually_atTop.2 ⟨N, hN⟩
