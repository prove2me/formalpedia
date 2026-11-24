-- Prove2me | solution 1 for MomentComparison.complexMomentNorm_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:17:37.401442+00:00
-- url     : https://prove2.me/submissions/7792578e-e04f-49c5-a0c0-cdfed5d62aca

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_MomentNorm
public import Theorems.Thm_MomentComparison_cubeAverage_nonneg
public import Theorems.Thm_MomentComparison_complexMoment_interpolate

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n : ℕ} (f : Cube n → ℂ) {p r u : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hu : 0 < u) (hu' : u < 1)
    (heq : r = (1 - u) + u * p) :
    complexMomentNorm r f ≤
      complexMomentNorm 1 f ^ ((1 - u) / r) *
      complexMomentNorm p f ^ (u * p / r) := by
  have hleft := complexMoment_interpolate f (a := 1) (b := p)
    zero_le_one hp.le hu hu'
  rw [mul_one, ← heq] at hleft
  have h := Real.rpow_le_rpow (cubeAverage_nonneg fun _ =>
    Real.rpow_nonneg (norm_nonneg _) _) hleft (inv_nonneg.mpr hr.le)
  have ha : 0 ≤ cubeAverage (fun x => ‖f x‖ ^ (1 : ℝ)) :=
    cubeAverage_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hb : 0 ≤ cubeAverage (fun x => ‖f x‖ ^ p) :=
    cubeAverage_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  unfold complexMomentNorm
  rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _) ] at h
  rw [← Real.rpow_mul ha, ← Real.rpow_mul hb] at h
  rw [inv_one, Real.rpow_one, ← Real.rpow_mul hb]
  convert h using 2 <;> congr 1
  field_simp
end MomentComparison
