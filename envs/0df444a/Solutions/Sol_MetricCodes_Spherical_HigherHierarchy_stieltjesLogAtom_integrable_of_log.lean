-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.stieltjesLogAtom_integrable_of_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.744009+00:00
-- url     : https://prove2.me/submissions/49ba8d73-4d01-428b-9cd5-bc816d2ce848

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {x : ℝ} (hx : 0 ≤ x)
    (hsupport : ∀ᵐ t ∂μ, 0 < t ∧ t ≤ 1)
    (hlog : Integrable (fun t : ℝ => Real.log t) μ) :
    Integrable (stieltjesLogAtom x) μ := by
  rcases hx.eq_or_lt with rfl | hx
  · have hzero : stieltjesLogAtom 0 = (0 : ℝ → ℝ) := by
      funext t
      by_cases ht : t = 0 <;> simp [stieltjesLogAtom, ht]
    rw [hzero]
    exact integrable_zero _ _ _
  · let C : ℝ := max |Real.log x| |Real.log (1 + x)|
    have hshift : Integrable (fun t : ℝ => Real.log (t + x)) μ := by
      apply (integrable_const (α := ℝ) (μ := μ) (c := C)).mono'
        (measurable_id.add measurable_const).log.aestronglyMeasurable
      filter_upwards [hsupport] with t ht
      have htx : 0 < t + x := add_pos ht.1 hx
      have hone : 0 < 1 + x := by linarith
      have hlower : Real.log x ≤ Real.log (t + x) :=
        Real.strictMonoOn_log.monotoneOn
          (show x ∈ Set.Ioi 0 from hx)
          (show t + x ∈ Set.Ioi 0 from htx)
          (by linarith [ht.1])
      have hupper : Real.log (t + x) ≤ Real.log (1 + x) :=
        Real.strictMonoOn_log.monotoneOn
          (show t + x ∈ Set.Ioi 0 from htx)
          (show 1 + x ∈ Set.Ioi 0 from hone)
          (by linarith [ht.2])
      simp only [Pi.add_apply, id_eq]
      change |Real.log (t + x)| ≤ C
      apply (abs_le).2
      constructor
      · exact (neg_le_neg (le_max_left _ _)).trans
          ((neg_abs_le (Real.log x)).trans hlower)
      · exact hupper.trans
          ((le_abs_self _).trans (le_max_right _ _))
    apply (hshift.sub hlog).congr
    filter_upwards [hsupport] with t ht
    unfold stieltjesLogAtom
    exact (Real.log_div (by linarith) ht.1.ne').symm
end MetricCodes.Spherical.HigherHierarchy
