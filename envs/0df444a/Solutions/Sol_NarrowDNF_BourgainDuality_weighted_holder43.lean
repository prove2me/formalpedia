-- Prove2me | solution 1 for NarrowDNF.BourgainDuality.weighted_holder43
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:03:50.982222+00:00
-- url     : https://prove2.me/submissions/e8c60375-7946-4f3f-addb-6a363656ca1a

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_NarrowDNF_BourgainDuality

namespace NarrowDNF.BourgainDuality
end NarrowDNF.BourgainDuality


noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainDuality
variable {α : Type*} [Fintype α]
/-- Weighted Hölder, with exponents 4/3 and 4. -/
theorem solution (w f g : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    |∑ x, w x * f x * g x| ≤
      moment43 w f ^ (3/4 : ℝ) * (∑ x, w x * g x ^ 4) ^ (1/4 : ℝ) := by
  have hc : Real.HolderConjugate (4/3) 4 := by
    constructor <;> norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hc
    (f := fun x => w x ^ (3/4 : ℝ) * |f x|)
    (g := fun x => w x ^ (1/4 : ℝ) * |g x|)
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (abs_nonneg _))
    (fun x _ => mul_nonneg (Real.rpow_nonneg (hw x) _) (abs_nonneg _))
  have hweight (x : α) : w x ^ (3/4 : ℝ) * w x ^ (1/4 : ℝ) = w x := by
    rw [← Real.rpow_add' (hw x) (by norm_num : (3/4 : ℝ)+(1/4 : ℝ) ≠ 0)]
    norm_num
  have hf (x : α) : (w x ^ (3/4 : ℝ) * |f x|) ^ (4/3 : ℝ) =
      w x * |f x| ^ (4/3 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw x) _) (abs_nonneg _),
      ← Real.rpow_mul (hw x)]
    norm_num
  have hg (x : α) : (w x ^ (1/4 : ℝ) * |g x|) ^ (4 : ℝ) = w x * g x ^ 4 := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hw x) _) (abs_nonneg _),
      ← Real.rpow_mul (hw x)]
    norm_num
    simp [← abs_pow, abs_of_nonneg (show 0 ≤ g x ^ 4 by positivity)]
  have hprod (x : α) : (w x ^ (3/4 : ℝ) * |f x|) *
      (w x ^ (1/4 : ℝ) * |g x|) = w x * |f x| * |g x| := by
    calc
      _ = (w x ^ (3/4 : ℝ) * w x ^ (1/4 : ℝ)) * |f x| * |g x| := by ring
      _ = _ := by rw [hweight]
  simp only [hf, hg, hprod] at h
  norm_num only at h
  calc
    _ ≤ ∑ x, |w x * f x * g x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, w x * |f x| * |g x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_mul, abs_of_nonneg (hw x)]
    _ ≤ _ := h
