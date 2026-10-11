-- Prove2me | solution 1 for HunterPDE.Newtonian.secondPartial_formula
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:42:37.310142+00:00
-- url     : https://prove2.me/submissions/ee9c5d2f-e9c3-4423-a6fc-85b5b18bbb13

import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open HunterPDE.Newtonian Filter
open scoped Topology

theorem solution (n : ℕ) (hn : 2 ≤ n) (i j : Fin n)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    secondPartial (fundamentalSolution n) i j z =
      -(1 / ((n : ℝ) * unitBallVolume n)) *
        (‖z‖ ^ (-(n : ℝ)) * (if i = j then 1 else 0) -
          (n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 2) * z i * z j) := by
  let a : ℝ := -(1 / ((n : ℝ) * unitBallVolume n))
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hgrad : partialDeriv (fundamentalSolution n) j =ᶠ[𝓝 z]
      (fun x : EuclideanSpace ℝ (Fin n) => a * (‖x‖ ^ (-(n : ℝ)) * x j)) := by
    filter_upwards [eventually_ne_nhds hz] with x hx
    rw [(fundamentalSolution_partial n hn).2 x hx j]
    dsimp [a]
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_natCast]
    have hp : ‖x‖ ^ n = ‖x‖ ^ (n - 1) * ‖x‖ := by
      have he : n = (n - 1) + 1 := by omega
      calc
        ‖x‖ ^ n = ‖x‖ ^ ((n - 1) + 1) := congrArg (fun k : ℕ => ‖x‖ ^ k) he
        _ = _ := pow_succ _ _
    rw [hp]
    ring
  have hnorm : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z :=
    (contDiffAt_norm (𝕜 := ℝ) (n := 1) hz).differentiableAt (by simp)
  have hd := ((hnorm.hasFDerivAt.rpow_const (p := -(n : ℝ)) (Or.inl hr.ne')).mul
    (EuclideanSpace.proj j).hasFDerivAt).const_mul a
  have hdi : fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z
      (EuclideanSpace.single i 1) = z i / ‖z‖ := by
    have he := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.single i 1)) (hnorm.hasFDerivAt.pow 2).fderiv
    rw [fderiv_norm_sq_apply] at he
    simp [EuclideanSpace.inner_single_right] at he
    apply (eq_div_iff hr.ne').2
    nlinarith
  change HasFDerivAt
    (fun x : EuclideanSpace ℝ (Fin n) => a * (‖x‖ ^ (-(n : ℝ)) * x j)) _ z at hd
  change fderiv ℝ (partialDeriv (fundamentalSolution n) j) z
    (EuclideanSpace.single i 1) = _
  rw [hgrad.fderiv_eq, hd.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul, hdi]
  have hp : ‖z‖ ^ (-(n : ℝ) - 1) / ‖z‖ = ‖z‖ ^ (-(n : ℝ) - 2) := by
    calc
      _ = ‖z‖ ^ (-(n : ℝ) - 1) / ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖z‖ ^ (-(n : ℝ) - 1 - 1) := (Real.rpow_sub hr _ _).symm
      _ = _ := by congr 1; ring
  dsimp [a]
  have hp' : ‖z‖ ^ (-(n : ℝ) - 1) = ‖z‖ ^ (-(n : ℝ) - 2) * ‖z‖ := by
    exact (div_eq_iff hr.ne').mp hp
  rw [hp']
  split_ifs with h
  · subst j
    simp
    field_simp
    ring_nf
    simp
  · simp [Ne.symm h]
    field_simp
    ring_nf
    simp
