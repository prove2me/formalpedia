-- Prove2me | solution 1 for HuImkellerMuller.Exponential.v_nonneg_and_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:51:29.928982+00:00
-- url     : https://prove2.me/submissions/fb238f69-eaca-4740-80d0-ba2fc349de05

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace Aux_HIM_V
open HuImkellerMuller.Exponential

lemma alg (α P Zi N Q d : ℝ) (hα : α ≠ 0) :
    -α * P + α * (-(α / 2) * d ^ 2 + Zi + 1 / (2 * α) * N ^ 2) + 1 / 2 * α ^ 2 * Q ^ 2 =
      1 / 2 * α ^ 2 * ((Q ^ 2 - 2 * ((1 / α) * (P - Zi)) + ((1 / α) * N) ^ 2) - d ^ 2) := by
  field_simp
  ring

lemma key {m : ℕ} (C : Set (EuclideanSpace ℝ (Fin m))) (θ z : EuclideanSpace ℝ (Fin m))
    (α : ℝ) (hα : 0 < α) (p : EuclideanSpace ℝ (Fin m)) :
    vfun C θ α p z = 1 / 2 * α ^ 2 *
      (‖p - (z + (1 / α) • θ)‖ ^ 2 - Metric.infDist (z + (1 / α) • θ) C ^ 2) := by
  have e1 : p - (z + (1 / α) • θ) = (p - z) - (1 / α) • θ := by abel
  rw [e1, norm_sub_sq_real, real_inner_smul_right, inner_sub_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / α)]
  unfold vfun drv
  exact alg α _ _ _ _ _ hα.ne'

end Aux_HIM_V

open HuImkellerMuller.Exponential Aux_HIM_V in
theorem solution {m : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin m))) (hC : IsClosed C)
    (θ z : EuclideanSpace ℝ (Fin m)) (α : ℝ) (hα : 0 < α) :
    (∀ p ∈ C, 0 ≤ vfun C θ α p z) ∧
      ∀ p ∈ proj C (z + (1 / α) • θ), vfun C θ α p z = 0 := by
  constructor
  · intro p hp
    rw [key C θ z α hα p]
    have h := Metric.infDist_le_dist_of_mem (x := z + (1 / α) • θ) hp
    rw [dist_eq_norm, norm_sub_rev] at h
    have hd0 := Metric.infDist_nonneg (x := z + (1 / α) • θ) (s := C)
    have h2 := pow_le_pow_left₀ hd0 h 2
    exact mul_nonneg (by positivity) (sub_nonneg.mpr h2)
  · intro p hp
    rw [key C θ z α hα p, norm_sub_rev, hp.2]
    ring
