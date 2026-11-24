-- Prove2me | solution 1 for MomentComparison.polynomialGrowth_of_disk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:04:02.475038+00:00
-- url     : https://prove2.me/submissions/a1977cad-6bb5-490a-831d-354ccd349a08

module
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Definitions.Def_MomentComparison_Lens
public import Definitions.Def_MomentComparison_ComplexPower
public import Definitions.Def_MomentComparison_LensAngle
public import Definitions.Def_MomentComparison_LensEvaluation
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_MomentComparison_Conformal

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Set Metric
open MomentComparison
namespace MomentComparison
theorem _root_.solution (P : Polynomial ℂ) {d : ℕ} (hP : P.natDegree ≤ d)
    {g : ℂ → ℂ} (hg : DiffContOnCl ℂ g (ball 0 1))
    {M : ℝ} (hbound : ∀ t ∈ sphere (0 : ℂ) 1, ‖P.eval (g t / t)‖ ≤ M)
    {t : ℂ} (ht : t ∈ closedBall 0 1) (ht0 : t ≠ 0) :
    ‖P.eval (g t / t)‖ ≤ ‖t‖⁻¹ ^ d * M := by
  let F (s : ℂ) := ∑ i ∈ Finset.range (d + 1), P.coeff i * g s ^ i * s ^ (d - i)
  have hF : DiffContOnCl ℂ F (ball 0 1) := by
    constructor
    · exact DifferentiableOn.fun_sum fun i _ =>
        ((hg.differentiableOn.pow i).const_mul _).mul (differentiableOn_id.pow _)
    · exact continuousOn_finsetSum _ fun i _ =>
        ((hg.continuousOn.pow i).const_mul _).mul (continuousOn_id.pow _)
  have hF_eq (s : ℂ) (hs : s ≠ 0) : F s = s ^ d * P.eval (g s / s) := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow]
    have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have he : s ^ d = s ^ i * s ^ (d - i) := by
      rw [← pow_add, Nat.add_sub_of_le hi']
    rw [he]
    field_simp
  have hF_bound (s : ℂ) (hs : s ∈ frontier (ball (0 : ℂ) 1)) : ‖F s‖ ≤ M := by
    rw [frontier_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hs
    have hnorm := mem_sphere_zero_iff_norm.mp hs
    have hs0 : s ≠ 0 := by
      intro h
      simp [h] at hnorm
    rw [hF_eq s hs0, norm_mul, norm_pow, hnorm, one_pow, one_mul]
    exact hbound s hs
  have ht' : t ∈ closure (ball (0 : ℂ) 1) := by
    rwa [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hF hF_bound ht'
  rw [hF_eq t ht0, norm_mul, norm_pow] at h
  rw [inv_pow, ← div_eq_inv_mul]
  exact (le_div_iff₀ (pow_pos (norm_pos_iff.mpr ht0) _)).2 (by simpa [mul_comm] using h)
end MomentComparison
