-- Prove2me | solution 1 for MomentComparison.realMomentNorm_le_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:17:25.97635+00:00
-- url     : https://prove2.me/submissions/e208c8a6-e459-4035-9ac6-7b0cba3fa122

module
public import Definitions.Def_MomentComparison_Pairing
public import Definitions.Def_MomentComparison_Conformal
public import Definitions.Def_MomentComparison_Hypercontractivity
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Real.ConjExponents
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Upper
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeAverage_nonneg
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.cubeAverage_const
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.walsh_empty



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n : ℕ} {p q M : ℝ} (hp : 2 < p)
    (hpq : p.HolderConjugate q) (hM : 0 ≤ M) (f : Cube n → ℝ)
    (hbound : ∀ g : Cube n → ℂ,
      ‖(∑ x, (f x : ℂ) * g x) / (2 : ℂ) ^ n‖ ≤ M * complexMomentNorm q g) :
    complexMomentNorm p (fun x => (f x : ℂ)) ≤ M := by
  let g : Cube n → ℂ := fun x => (f x * |f x| ^ (p - 2) : ℝ)
  let A := cubeAverage fun x => |f x| ^ p
  have hp0 : p ≠ 0 := by linarith
  have hp2 : 0 ≤ p - 2 := by linarith
  have hA : 0 ≤ A := cubeAverage_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hnorm : complexMomentNorm p (fun x => (f x : ℂ)) = A ^ p⁻¹ := by
    simp only [A, complexMomentNorm, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  by_cases hA0 : A = 0
  · rw [hA0, Real.zero_rpow (inv_ne_zero hp0)]
    exact hM
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hg (x) : ‖g x‖ = |f x| ^ (p - 1) := by
    unfold g
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      |f x| * |f x| ^ (p - 2) = |f x| ^ (1 : ℝ) * |f x| ^ (p - 2) := by
        rw [Real.rpow_one]
      _ = |f x| ^ (1 + (p - 2)) := by
        rw [Real.rpow_add_of_nonneg (abs_nonneg _) zero_le_one hp2]
      _ = |f x| ^ (p - 1) := by congr 1; ring
  have hg' (x) : ‖g x‖ ^ q = |f x| ^ p := by
    rw [hg, ← Real.rpow_mul (abs_nonneg _), hpq.sub_one_mul_conj]
  have hgNorm : complexMomentNorm q g = A ^ q⁻¹ := by
    simp only [complexMomentNorm, A, hg']
  have hterm (x) : (f x : ℂ) * g x = ((|f x| ^ p : ℝ) : ℂ) := by
    unfold g
    rw [← Complex.ofReal_mul]
    congr 1
    have hrpow2 : f x * f x = |f x| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs, pow_two]
    rw [← mul_assoc, hrpow2, ← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) hp2]
    congr 1
    ring
  have hpair : (∑ x, (f x : ℂ) * g x) / (2 : ℂ) ^ n = (A : ℂ) := by
    simp only [hterm, A, cubeAverage, Complex.ofReal_div, Complex.ofReal_sum,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
  have h := hbound g
  rw [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA, hgNorm] at h
  refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hApos q⁻¹)
  rwa [← Real.rpow_add hApos, hpq.inv_add_inv_eq_one, Real.rpow_one]
end MomentComparison
