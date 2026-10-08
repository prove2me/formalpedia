-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.unbounded_packet_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:12:14.715556+00:00
-- url     : https://prove2.me/submissions/aa97bf13-5588-4fc3-8c02-bef69de4b07a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_local_logarithmic_interpolation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_logarithmic_jet_gluing
import Mathlib.Tactic.NormNum

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    ∀ y : Row d H → ℂ, ∃ P : MvPolynomial (Fin (d.m + 1)) ℂ,
      ∀ ρ : Row d H,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
          (FormalInterpolation.formalJet
            (fun i => (ρ.1.val : ℂ) * MatrixArithmetic.rationalCenters
              (finiteNumerators d) (finiteDenominators d) i) P) = y ρ := by
  classical
  intro y
  let c : Fin d.K → Fin d.m → ℂ := fun j i =>
    (j.val : ℂ) * MatrixArithmetic.rationalCenters
      (finiteNumerators d) (finiteDenominators d) i
  have hc : Function.Injective c := by
    let i : Fin d.m := ⟨0, by have hm := d.m_pos; omega⟩
    have hp : (finiteNumerators d i : ℂ) ≠ 0 := by
      exact_mod_cast (d.approximations i.val).2.1
    have hq : (finiteDenominators d i : ℂ) ≠ 0 := by
      have hqnat : d.q i.val ≠ 0 := by have h := (d.approximations i.val).1; omega
      exact_mod_cast hqnat
    have hr : MatrixArithmetic.rationalCenters
        (finiteNumerators d) (finiteDenominators d) i ≠ 0 := by
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hp) hq
    intro j k hjk
    have hmul := congrFun hjk i
    have hcast : (j.val : ℂ) = (k.val : ℂ) := mul_right_cancel₀ hr hmul
    apply Fin.ext
    exact_mod_cast hcast
  let S := OAI.PiExponent.strictWeightedSimplex
    (InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d))) H
  have hlocal : ∀ j : Fin d.K,
      ∃ Q : MvPolynomial (Fin (d.m + 1)) ℂ, ∀ a : ↥S,
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.val)
          (FormalInterpolation.formalJet (c j) Q) = y (j, a) := by
    intro j
    exact FormalInterpolation.finite_local_logarithmic_interpolation (c j) S
      (fun a => y (j, a))
  choose Q hQ using hlocal
  obtain ⟨P, hP⟩ := FormalInterpolation.finite_logarithmic_jet_gluing c hc S Q
  refine ⟨P, ?_⟩
  intro ρ
  exact (hP ρ.1 ρ.2).trans (hQ ρ.1 ρ.2)
