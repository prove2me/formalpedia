-- Prove2me | solution 1 for HunterPDE.Newtonian.norm_fderiv_secondPartial_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:52:06.397778+00:00
-- url     : https://prove2.me/submissions/da30598b-a977-48bb-9d3a-ec529dd00aed

import Theorems.Thm_HunterPDE_Newtonian_secondPartial_formula
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open HunterPDE.Newtonian Filter
open scoped Topology

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : Fin n,
      ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      DifferentiableAt ℝ (secondPartial (fundamentalSolution n) i j) z ∧
      ‖fderiv ℝ (secondPartial (fundamentalSolution n) i j) z‖ ≤
        C * ‖z‖ ^ (-(n : ℝ) - 1) := by
  let a : ℝ := -(1 / ((n : ℝ) * unitBallVolume n))
  refine ⟨‖a‖ * ((n : ℝ) + (n : ℝ) * ((n : ℝ) + 4)), by positivity, ?_⟩
  intro i j z hz
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm : DifferentiableAt ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z :=
    (contDiffAt_norm (𝕜 := ℝ) (n := 1) hz).differentiableAt (by simp)
  let D := fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) z
  have hD : ‖D‖ ≤ 1 := norm_fderiv_le_of_lipschitz ℝ
    (f := fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (x₀ := z) lipschitzWith_one_norm
  have hproj (k : Fin n) : ‖(EuclideanSpace.proj k :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    simpa using PiLp.norm_apply_le v k
  have hcoord (k : Fin n) : ‖z k‖ ≤ ‖z‖ := PiLp.norm_apply_le z k
  have hp (p : ℝ) := hnorm.hasFDerivAt.rpow_const (p := p) (Or.inl hr.ne')
  have hpn (p : ℝ) : ‖(p * ‖z‖ ^ (p - 1)) • D‖ ≤
      |p| * ‖z‖ ^ (p - 1) := by
    rw [norm_smul, norm_mul, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    exact mul_le_of_le_one_right (by positivity) hD
  let Q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    z i • EuclideanSpace.proj j + z j • EuclideanSpace.proj i
  have hQ : ‖Q‖ ≤ 2 * ‖z‖ := by
    calc
      _ ≤ ‖z i • EuclideanSpace.proj j‖ + ‖z j • EuclideanSpace.proj i‖ := norm_add_le _ _
      _ ≤ ‖z‖ * 1 + ‖z‖ * 1 := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul (hcoord i) (hproj j) (by positivity) (by positivity))
          (mul_le_mul (hcoord j) (hproj i) (by positivity) (by positivity))
      _ = _ := by ring
  let P (p : ℝ) := ‖z‖ ^ p • Q + (z i * z j) • ((p * ‖z‖ ^ (p - 1)) • D)
  have hP (p : ℝ) : ‖P p‖ ≤ (2 + |p|) * ‖z‖ ^ (p + 1) := by
    have he1 : ‖z‖ ^ p * ‖z‖ = ‖z‖ ^ (p + 1) := by
      simpa using (Real.rpow_add hr p 1).symm
    have he2 : ‖z‖ * ‖z‖ * ‖z‖ ^ (p - 1) = ‖z‖ ^ (p + 1) := by
      calc
        _ = ‖z‖ ^ (2 : ℝ) * ‖z‖ ^ (p - 1) := by rw [Real.rpow_two]; ring
        _ = ‖z‖ ^ (2 + (p - 1)) := (Real.rpow_add hr _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ ≤ ‖‖z‖ ^ p • Q‖ + ‖(z i * z j) • ((p * ‖z‖ ^ (p - 1)) • D)‖ := norm_add_le _ _
      _ ≤ ‖z‖ ^ p * (2 * ‖z‖) + (‖z‖ * ‖z‖) * (|p| * ‖z‖ ^ (p - 1)) := by
        simp only [norm_smul, norm_mul,
          Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
        exact add_le_add (mul_le_mul_of_nonneg_left hQ (by positivity))
          (mul_le_mul (mul_le_mul (hcoord i) (hcoord j) (by positivity) (by positivity))
            (by simpa only [norm_smul, norm_mul,
              Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)] using hpn p)
            (by positivity) (by positivity))
      _ = 2 * (‖z‖ ^ p * ‖z‖) + |p| * (‖z‖ * ‖z‖ * ‖z‖ ^ (p - 1)) := by ring
      _ = _ := by rw [he1, he2]; ring
  let d : ℝ := if i = j then 1 else 0
  have hd : |d| ≤ 1 := by dsimp [d]; split_ifs <;> norm_num
  let L := a • (d • ((-(n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1)) • D) - (n : ℝ) • P (-(n : ℝ) - 2))
  have hpi : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => x i)
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) z :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt
  have hpj : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => x j)
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) z :=
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt
  have hform : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin n) => a *
        (‖x‖ ^ (-(n : ℝ)) * d - (n : ℝ) * (‖x‖ ^ (-(n : ℝ) - 2) * (x i * x j)))) L z := by
    convert! (((hp (-(n : ℝ))).mul_const d).sub
      (((hp (-(n : ℝ) - 2)).mul (hpi.mul hpj)).const_mul (n : ℝ))).const_mul a using 1
  have heq : secondPartial (fundamentalSolution n) i j =ᶠ[𝓝 z]
      (fun x : EuclideanSpace ℝ (Fin n) => a *
        (‖x‖ ^ (-(n : ℝ)) * d - (n : ℝ) * (‖x‖ ^ (-(n : ℝ) - 2) * (x i * x j)))) := by
    filter_upwards [eventually_ne_nhds hz] with x hx
    rw [secondPartial_formula n hn i j x hx]
    dsimp [a, d]
    ring
  have hder := hform.congr_of_eventuallyEq heq
  refine ⟨hder.differentiableAt, ?_⟩
  rw [hder.fderiv]
  have ht1 : ‖d • ((-(n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1)) • D)‖ ≤
      (n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ 1 * (|-(n : ℝ)| * ‖z‖ ^ (-(n : ℝ) - 1)) :=
        mul_le_mul hd (hpn (-(n : ℝ))) (by positivity) (by positivity)
      _ = _ := by simp
  have ht2 : ‖(n : ℝ) • P (-(n : ℝ) - 2)‖ ≤
      (n : ℝ) * ((n : ℝ) + 4) * ‖z‖ ^ (-(n : ℝ) - 1) := by
    rw [norm_smul, Real.norm_natCast]
    calc
      _ ≤ (n : ℝ) * ((2 + |-(n : ℝ) - 2|) * ‖z‖ ^ (-(n : ℝ) - 2 + 1)) :=
        mul_le_mul_of_nonneg_left (hP (-(n : ℝ) - 2)) (Nat.cast_nonneg n (α := ℝ))
      _ = _ := by
        rw [abs_of_nonpos (show -(n : ℝ) - 2 ≤ 0 by linarith [Nat.cast_nonneg n (α := ℝ)])]
        have he : -(n : ℝ) - 2 + 1 = -(n : ℝ) - 1 := by ring
        rw [he]
        ring
  calc
    ‖L‖ ≤ ‖a‖ * (‖d • ((-(n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1)) • D)‖ + ‖(n : ℝ) • P (-(n : ℝ) - 2)‖) := by
      dsimp only [L]
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg a)
    _ ≤ ‖a‖ * ((n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 1) + (n : ℝ) * ((n : ℝ) + 4) * ‖z‖ ^ (-(n : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (norm_nonneg a)
    _ = _ := by ring
