-- Prove2me | solution 1 for HunterPDE.Newtonian.norm_secondPartial_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T10:35:32.634053+00:00
-- url     : https://prove2.me/submissions/26304c12-0126-4d8c-ad3e-547f74a206a1

import Theorems.Thm_HunterPDE_Newtonian_fundamentalSolution_partial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open HunterPDE.Newtonian Filter
open scoped Topology

theorem solution (n : ℕ) (hn : 2 ≤ n) (i j : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      ‖secondPartial (fundamentalSolution n) i j z‖ ≤ C * ‖z‖ ^ (-(n : ℝ)) := by
  let a : ℝ := -(1 / ((n : ℝ) * unitBallVolume n))
  refine ⟨‖a‖ * (1 + n), by positivity, ?_⟩
  intro z hz
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
  change HasFDerivAt
    (fun x : EuclideanSpace ℝ (Fin n) => a * (‖x‖ ^ (-(n : ℝ)) * x j)) _ z at hd
  have heq : secondPartial (fundamentalSolution n) i j z =
      a * (‖z‖ ^ (-(n : ℝ)) * (EuclideanSpace.single i (1 : ℝ)) j +
        z j * ((-(n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1)) *
          fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z
            (EuclideanSpace.single i 1))) := by
    change fderiv ℝ (partialDeriv (fundamentalSolution n) j) z
      (EuclideanSpace.single i 1) = _
    rw [hgrad.fderiv_eq, hd.fderiv]
    simp
    split_ifs <;> ring
  have hb : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
  have hdn : ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z
      (EuclideanSpace.single i 1)‖ ≤ 1 := by
    calc
      _ ≤ ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z‖ *
          ‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 := by
        rw [hb, mul_one]
        exact norm_fderiv_le_of_lipschitz ℝ
          (f := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (x₀ := z)
          lipschitzWith_one_norm
  have hc : ‖(EuclideanSpace.single i (1 : ℝ)) j‖ ≤ 1 := by
    simpa [hb] using (PiLp.norm_apply_le (EuclideanSpace.single i (1 : ℝ)) j)
  have hzj : ‖z j‖ ≤ ‖z‖ := PiLp.norm_apply_le z j
  have hp : ‖z‖ ^ (-(n : ℝ) - 1) * ‖z‖ = ‖z‖ ^ (-(n : ℝ)) := by
    calc
      _ = ‖z‖ ^ (-(n : ℝ) - 1) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = ‖z‖ ^ (-(n : ℝ) - 1 + 1) := (Real.rpow_add hr _ _).symm
      _ = _ := by congr 1; ring
  rw [heq, norm_mul]
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg a)
  calc
    _ ≤ ‖‖z‖ ^ (-(n : ℝ)) * (EuclideanSpace.single i (1 : ℝ)) j‖ +
        ‖z j * ((-(n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1)) *
          fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z
            (EuclideanSpace.single i 1))‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ (-(n : ℝ)) + (n : ℝ) * ‖z‖ ^ (-(n : ℝ)) := by
      simp only [norm_mul, norm_neg, Real.norm_natCast,
        Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_left hc
          (Real.rpow_nonneg (norm_nonneg z) (-(n : ℝ)))
      · calc
          ‖z j‖ * ((n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1) *
              ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z
                (EuclideanSpace.single i 1)‖) ≤
              ‖z‖ * ((n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1) * 1) :=
            mul_le_mul hzj
              (mul_le_mul_of_nonneg_left hdn (by positivity))
              (by positivity) (norm_nonneg z)
          _ = (n : ℝ) * (‖z‖ ^ (-(n : ℝ) - 1) * ‖z‖) := by ring
          _ = _ := by rw [hp]
    _ = (1 + n) * ‖z‖ ^ (-(n : ℝ)) := by ring
