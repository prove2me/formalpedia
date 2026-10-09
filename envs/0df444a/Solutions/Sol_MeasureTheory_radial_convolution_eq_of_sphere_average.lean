-- Prove2me | solution 1 for MeasureTheory.radial_convolution_eq_of_sphere_average
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T11:13:38.206043+00:00
-- url     : https://prove2.me/submissions/df40c40e-369c-42c1-9ac1-24c2b5277b95

import Theorems.Thm_MeasureTheory_integral_polar_sphere_centered
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory Set Metric Filter
open scoped Topology Convolution
set_option autoImplicit false

theorem solution {n : ℕ} (hn : 0 < n)
    {k g : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ → ℝ} {R : ℝ}
    (hk : Continuous k) (hkc : HasCompactSupport k)
    (hkr : ∀ y, k y = κ ‖y‖) (hks : ∀ y, R ≤ ‖y‖ → k y = 0)
    (hki : ∫ y, k y = 1) (hg : LocallyIntegrable g)
    (x : EuclideanSpace ℝ (Fin n))
    (hmean : ∀ r : ℝ, 0 < r → r < R →
      (⨍ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g (x + r • ω.1) ∂volume.toSphere) = g x) :
    (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x = g x := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := sphere (0 : E) 1
  let f : E → ℝ := fun y => k (x - y) * g y
  let c : E → ℝ := fun y => k (x - y) * g x
  have hf : Integrable f := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (hkc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hg x).integrable_swap
  have hc : Integrable c :=
    ((hk.integrable_of_hasCompactSupport hkc).comp_sub_left x).mul_const _
  have inner : ∀ t : Ioi (0 : ℝ),
      (∫ ω : S, f (x + t.1 • ω.1) ∂volume.toSphere) =
      ∫ ω : S, c (x + t.1 • ω.1) ∂volume.toSphere := by
    intro t
    have htpos : 0 < t.1 := t.2
    have hnorm : ∀ ω : S, ‖x - (x + t.1 • ω.1)‖ = t.1 := by
      intro ω
      simp [norm_smul, (mem_sphere_zero_iff_norm.mp ω.2), abs_of_pos htpos]
    by_cases ht : t.1 < R
    · have hav := hmean t.1 t.2 ht
      have hi := congrArg (fun a : ℝ => (volume.toSphere : Measure S).real univ • a) hav
      rw [measure_smul_average, ← integral_const] at hi
      simp only [f, c, hkr, hnorm]
      rw [integral_const_mul, integral_const_mul, hi]
    · have hz : ∀ ω : S, k (x - (x + t.1 • ω.1)) = 0 :=
        fun ω => hks _ (by rw [hnorm]; exact le_of_not_gt ht)
      simp only [f, c, hz, zero_mul]
  have heq : (∫ y, f y) = ∫ y, c y := by
    rw [integral_polar_sphere_centered hn x f hf,
      integral_polar_sphere_centered hn x c hc]
    exact integral_congr_ae (Eventually.of_forall inner)
  rw [convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  change (∫ y, f y) = g x
  rw [heq]
  simp only [c, integral_mul_const, integral_sub_left_eq_self]
  change (∫ y, k y) * g x = g x
  rw [hki, one_mul]
