-- Prove2me | solution 1 for Kyprianou.Ch04.bvUniformSetIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:33:03.910679+00:00
-- url     : https://prove2.me/submissions/295c9547-4336-4b16-9796-ae8ef6bcc9e1

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_Kyprianou_Ch04_bvUniformLimitIntegrableOnV1
open MeasureTheory Filter Set
set_option autoImplicit false

theorem solution
    {I A : Type} [MeasurableSpace A] (L : Filter I) [L.NeBot]
    (μ : Measure A) (s : Set A) (hs : MeasurableSet s) (hμ : μ s < ⊤)
    (F : I → A → ℝ) (g : A → ℝ)
    (hF : ∀ i, IntegrableOn (F i) s μ)
    (hU : TendstoUniformlyOn F g L s) :
    Tendsto (fun i => ∫ x in s, F i x ∂μ) L (nhds (∫ x in s, g x ∂μ)) := by
  have hg := Kyprianou.Ch04.bvUniformLimitIntegrableOnV1 L μ s hs hμ F g hF hU
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hm : 0 ≤ μ.real s := ENNReal.toReal_nonneg
  let δ := ε / (μ.real s + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) δ hδ] with i hi
  rw [dist_eq_norm, ← integral_sub (hF i) hg]
  calc
    _ ≤ δ * μ.real s := by
      apply norm_setIntegral_le_of_norm_le_const hμ
      intro x hx
      have h := hi x hx
      rw [dist_comm, dist_eq_norm] at h
      exact h.le
    _ < ε := by
      dsimp [δ]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by linarith : 0 < μ.real s + 1)).2
      nlinarith
