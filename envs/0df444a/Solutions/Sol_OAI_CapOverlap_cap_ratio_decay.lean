-- Prove2me | solution 1 for OAI.CapOverlap.cap_ratio_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:49:55.883289+00:00
-- url     : https://prove2.me/submissions/4da1840c-5362-4a12-83ea-0bc894ba1221

import Mathlib
import Definitions.Def_OAIQ16Cd000
import Theorems.Thm_OAI_CapGeometry_halfcap_ratio

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapGeometry
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapGeometry
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
open SphericalLaw

lemma halfcap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (halfcap x t) :=
  isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)

lemma halfcap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (halfcap u.val t) := by
  apply positive_open _ (halfcap_open _ _) ⟨u, ?_⟩
  change t < inner ℝ u.val u.val
  simpa only [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.mp u.property, one_pow] using ht

end CapGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapOverlap
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapOverlap
open Set MeasureTheory Metric SphericalLaw CapGeometry CapLens

lemma cap_ratio_decay_oai {n : ℕ} [NeZero n] (e : Sphere n) {l u t s : ℝ}
    (hl : 0 < l) (hu : u < 1) (hlt : l ≤ t) (hts : t ≤ s) (hsu : s ≤ u)
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l) :
    (σ n).real (halfcap e.val s) ≤ Real.exp (-(n:ℝ)*l*(s-t)/2) *
      (σ n).real (halfcap e.val t) := by
  have hp : 0 < (σ n).real (halfcap e.val t) :=
    ENNReal.toReal_pos (ne_of_gt (halfcap_positive e ((hts.trans hsu).trans_lt hu)))
      (measure_ne_top _ _)
  have hc : ((1/l+1/(1-u^2))-(n:ℝ)*l)*(s-t) ≤ -(n:ℝ)*l*(s-t)/2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)*l/2-(1/l+1/(1-u^2)))
      (sub_nonneg.mpr hts)]
  exact ((div_le_iff₀ hp).mp (halfcap_ratio e hl hu hlt hts hsu).2).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc) hp.le)

end CapOverlap

end OAI
end

theorem solution : type_of% @OAI.CapOverlap.cap_ratio_decay_oai := @OAI.CapOverlap.cap_ratio_decay_oai
