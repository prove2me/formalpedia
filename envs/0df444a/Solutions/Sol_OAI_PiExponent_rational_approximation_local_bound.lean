-- Prove2me | solution 1 for OAI.PiExponent.rational_approximation_local_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T08:03:33.020517+00:00
-- url     : https://prove2.me/submissions/b3f83d0b-9321-4800-9f6f-0639e11c4d44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Theorems.Thm_OAI_PiExponent_determinant_budget_exists
import Theorems.Thm_OAI_PiExponent_separated_weight_logarithmic_interpolation
import Theorems.Thm_OAI_PiExponent_select_separated_denominators
import Theorems.Thm_OAI_PiExponent_logarithmic_determinant_obstruction

/- Reduction to separated-weight interpolation and determinant comparison.
Only the four imported child modules contain placeholders. -/
theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q → |(p : ℝ)| ≤ 4 * (q : ℝ) →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  classical
  by_contra htarget
  have hbad : ∀ N : ℕ, ∃ (p : ℤ) (q : ℕ),
      max N 2 ≤ q ∧ |Real.pi - (p : ℝ) / (q : ℝ)| < (q : ℝ) ^ (-nu) := by
    intro N
    by_contra hN
    apply htarget
    refine ⟨max N 2, le_max_right N 2, ?_⟩
    intro p q hq _
    by_contra he
    exact hN ⟨p, q, hq, lt_of_not_ge he⟩
  have hunbounded : ∀ L : ℕ, ∃ (p : ℤ) (q : ℕ),
      2 ≤ q ∧ p ≠ 0 ∧ L ≤ Nat.ceil (Real.log (q : ℝ)) ∧
        |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu) := by
    intro L
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (L : ℝ))
    obtain ⟨p, q, hq, he⟩ := hbad N
    have hq2 : 2 ≤ q := le_trans (le_max_right N 2) hq
    have hNq : N ≤ q := le_trans (le_max_left N 2) hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := le_trans (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_le.mpr hq2)
    have hpow : (q : ℝ) ^ (-nu) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
    have hp : p ≠ 0 := by
      intro hp0
      have hpi : Real.pi < (q : ℝ) ^ (-nu) := by
        simpa [hp0, abs_of_pos Real.pi_pos] using he
      linarith [Real.pi_gt_three]
    have hlog : (L : ℝ) ≤ Real.log (q : ℝ) := by
      calc
        (L : ℝ) = Real.log (Real.exp (L : ℝ)) := (Real.log_exp _).symm
        _ ≤ Real.log (q : ℝ) :=
          Real.log_le_log (Real.exp_pos _) (le_trans hN.le (Nat.cast_le.mpr hNq))
    have hceil : L ≤ Nat.ceil (Real.log (q : ℝ)) := by
      exact Nat.cast_le.mp (le_trans hlog (Nat.le_ceil (Real.log (q : ℝ))))
    exact ⟨p, q, hq2, hp, hceil, he.le⟩
  obtain ⟨B⟩ := OAI.PiExponent.determinant_budget_exists nu hnu
  obtain ⟨S, hS⟩ := OAI.PiExponent.separated_weight_logarithmic_interpolation
    B.m B.K B.m_pos B.K_pos B.w0 B.v0 B.theta
    B.w0_pos B.v0_pos B.theta_pos B.theta_lt_one
    B.volume_transverse B.volume_full
  obtain ⟨p, q, hfamily, hsep⟩ := OAI.PiExponent.select_separated_denominators
    (fun p q => |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu))
    hunbounded B.m B.wmin S
  let w : Fin B.m → ℕ := fun i => Nat.ceil (Real.log (q i : ℝ))
  have hmin : ∀ i, B.wmin ≤ w i := fun i => (hfamily i).2.2.1
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le B.wmin_pos (hmin i)
  exact OAI.PiExponent.logarithmic_determinant_obstruction nu hnu B p q w
    (fun i => (hfamily i).1) (fun i => (hfamily i).2.1)
    (fun _ => rfl) hmin (fun i => (hfamily i).2.2.2)
    (hS w hwpos hsep)