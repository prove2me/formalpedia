-- Prove2me | solution 1 for OAI.Paper256.posSemidef_three_of_principal_minors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:56:40.485622+00:00
-- url     : https://prove2.me/submissions/3f685f39-9a95-4027-8922-981b89a4bf50

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/FormPositive.lean:L69-L88
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.posSemidef_three_of_principal_minors. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks

-- ---- from OAI.Analysis.HyperbolicCones.FormPositive ----
namespace OAI

/-! Positivity of the Choi--Lam form, including its principal-minor argument. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace Paper256

private theorem quadratic_two_nonnegative (a b c x y : ℝ)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hdet : b ^ 2 ≤ a * c) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by nlinarith [sq_nonneg b]
    simpa [ha0, hb0] using mul_nonneg hc (sq_nonneg y)
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h := add_nonneg (sq_nonneg (a * x + b * y))
      (mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg y))
    have hm : 0 ≤ a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
      nlinarith only [h]
    exact nonneg_of_mul_nonneg_right hm hapos

private theorem quadratic_three_nonnegative (a b c d e f x y z : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 ≤ f)
    (hab : b ^ 2 ≤ a * d) (hac : c ^ 2 ≤ a * f) (hdf : e ^ 2 ≤ d * f)
    (hdet : 0 ≤ a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d) :
    0 ≤ a * x ^ 2 + d * y ^ 2 + f * z ^ 2 +
      2 * b * x * y + 2 * c * x * z + 2 * e * y * z := by
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by nlinarith [sq_nonneg b]
    have hc0 : c = 0 := by nlinarith [sq_nonneg c]
    have h := quadratic_two_nonnegative d e f y z hd hf hdf
    simpa [ha0, hb0, hc0, add_comm, add_left_comm, add_assoc] using h
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hsmall : (a * e - b * c) ^ 2 ≤ (a * d - b ^ 2) * (a * f - c ^ 2) := by
      nlinarith only [mul_nonneg ha hdet]
    have hs := quadratic_two_nonnegative (a * d - b ^ 2) (a * e - b * c)
      (a * f - c ^ 2) y z (sub_nonneg.mpr hab) (sub_nonneg.mpr hac) hsmall
    have hm : 0 ≤ a * (a * x ^ 2 + d * y ^ 2 + f * z ^ 2 +
        2 * b * x * y + 2 * c * x * z + 2 * e * y * z) := by
      nlinarith only [sq_nonneg (a * x + b * y + c * z), hs]
    exact nonneg_of_mul_nonneg_right hm hapos

/-- For a symmetric three-by-three matrix, its principal minors certify positivity. -/
theorem posSemidef_three_of_principal_minors (M : Mat 3 ℝ) (hM : M.IsHermitian)
    (hdiag : ∀ i, 0 ≤ M i i)
    (h01 : M 0 1 ^ 2 ≤ M 0 0 * M 1 1)
    (h02 : M 0 2 ^ 2 ≤ M 0 0 * M 2 2)
    (h12 : M 1 2 ^ 2 ≤ M 1 1 * M 2 2) (hdet : 0 ≤ Matrix.det M) :
    M.PosSemidef := by
  have h10 : M 1 0 = M 0 1 := by simpa using hM.apply 0 1
  have h20 : M 2 0 = M 0 2 := by simpa using hM.apply 0 2
  have h21 : M 2 1 = M 1 2 := by simpa using hM.apply 1 2
  have hd : 0 ≤ M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 ^ 2 -
      M 0 1 ^ 2 * M 2 2 + 2 * M 0 1 * M 0 2 * M 1 2 - M 0 2 ^ 2 * M 1 1 := by
    rw [Matrix.det_fin_three, h10, h20, h21] at hdet
    nlinarith only [hdet]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => ?_
  have h := quadratic_three_nonnegative (M 0 0) (M 0 1) (M 0 2)
    (M 1 1) (M 1 2) (M 2 2) (x 0) (x 1) (x 2)
    (hdiag 0) (hdiag 1) (hdiag 2) h01 h02 h12 hd
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, h10, h20, h21]
  nlinarith only [h]

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open scoped Matrix.Norms.L2Operator
open Matrix


theorem solution : type_of% @_root_.OAI.Paper256.posSemidef_three_of_principal_minors := @_root_.OAI.Paper256.posSemidef_three_of_principal_minors
