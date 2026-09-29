-- Prove2me | solution 1 for LanglandsTunnell.mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/84ea859f-ffc6-5b73-90b4-8564d585b0cb

import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin

set_option autoImplicit false

open MeasureTheory Set

namespace Ws23K3

theorem qmp_mul_left {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ => r * t) volume volume := by
  refine ⟨measurable_const_mul r, ?_⟩
  rw [Real.map_volume_mul_left hr]
  exact Measure.smul_absolutelyContinuous

theorem ae_restrict_comp_mul {g g' : ℝ → ℂ} (h : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), g u = g' u)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g (r * t) = g' (r * t) := by
  rw [ae_restrict_iff' measurableSet_Ioi] at h ⊢
  have h2 := (qmp_mul_left hr.ne').ae h
  filter_upwards [h2] with t ht htpos
  exact ht (mul_pos hr htpos)

theorem core (φ g : ℝ → ℂ) (z : ℂ)
    (hφm : AEStronglyMeasurable φ (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hgM : Measurable g)
    (hφ : MellinConvergent φ (1 - z)) (hg : MellinConvergent g z) :
    MellinConvergent (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z ∧
      mellin (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z = mellin φ (1 - z) * mellin g z := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  haveI : SFinite μ := inferInstance

  set F : ℝ × ℝ → ℂ := fun q => ((q.1 : ℂ) ^ (z - 1)) * (φ q.2 * g (q.1 * q.2)) with hF
  have hcpow : Measurable fun r : ℝ => (r : ℂ) ^ (z - 1) := Complex.measurable_ofReal.pow_const _
  have hFm : AEStronglyMeasurable F (μ.prod μ) := by
    refine ((hcpow.comp measurable_fst).aestronglyMeasurable).mul (hφm.comp_snd.mul ?_)
    exact (hgM.comp (measurable_fst.mul measurable_snd)).aestronglyMeasurable

  set N : ℝ → ℝ := fun u => u ^ (z.re - 1) * ‖g u‖ with hN
  set M : ℝ := ∫ u in Ioi (0 : ℝ), N u with hM
  have hnormF : ∀ {t : ℝ}, 0 < t → ∀ {r : ℝ}, 0 < r → ‖F (r, t)‖ = ‖φ t‖ * (t ^ (-(z.re - 1)) * N (t * r)) := by
    intro t ht r hr
    simp only [hF, hN, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.sub_re, Complex.one_re]
    rw [Real.mul_rpow ht.le hr.le, mul_comm r t]
    have : t ^ (-(z.re - 1)) * t ^ (z.re - 1) = 1 := by
      rw [Real.rpow_neg ht.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos ht _).ne']
    calc r ^ (z.re - 1) * (‖φ t‖ * ‖g (t * r)‖)
        = (t ^ (-(z.re - 1)) * t ^ (z.re - 1)) * r ^ (z.re - 1) * (‖φ t‖ * ‖g (t * r)‖) := by rw [this, one_mul]
      _ = ‖φ t‖ * (t ^ (-(z.re - 1)) * (t ^ (z.re - 1) * r ^ (z.re - 1) * ‖g (t * r)‖)) := by ring
  have hfibre : ∀ {t : ℝ}, 0 < t → ∫ r in Ioi (0 : ℝ), ‖F (r, t)‖ = M * (t ^ (-z.re) * ‖φ t‖) := by
    intro t ht
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => hnormF ht hr), integral_const_mul,
      integral_const_mul, integral_comp_mul_left_Ioi N 0 ht, mul_zero, smul_eq_mul]
    have : t ^ (-(z.re - 1)) * t⁻¹ = t ^ (-z.re) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; congr 1; ring
    calc ‖φ t‖ * (t ^ (-(z.re - 1)) * (t⁻¹ * M)) = (t ^ (-(z.re - 1)) * t⁻¹) * M * ‖φ t‖ := by ring
      _ = M * (t ^ (-z.re) * ‖φ t‖) := by rw [this]; ring

  have hφnorm : IntegrableOn (fun t : ℝ => t ^ (-z.re) * ‖φ t‖) (Ioi 0) := by
    have := (mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi hφm).1 hφ
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Complex.sub_re, Complex.one_re]
    ring_nf
  have hFint : Integrable F (μ.prod μ) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨(ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : t ∈ Ioi (0 : ℝ)) => ?_), ?_⟩
    · have h1 : Integrable (fun r : ℝ => ((r : ℂ) ^ (z - 1)) • g (t * r)) μ :=
        (MellinConvergent.comp_mul_left ht).2 hg
      refine (h1.const_mul (φ t)).congr (ae_of_all _ fun r => ?_)
      simp only [hF, smul_eq_mul, mul_comm t r]
      ring
    · refine (hφnorm.const_mul M).congr ?_
      exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => (hfibre ht).symm)

  have hT : ∀ r : ℝ, ((r : ℂ) ^ (z - 1)) • (∫ t in Ioi (0 : ℝ), φ t * g (r * t)) = ∫ t, F (r, t) ∂μ := by
    intro r
    rw [smul_eq_mul, ← integral_const_mul]
  refine ⟨?_, ?_⟩
  · show Integrable (fun r : ℝ => ((r : ℂ) ^ (z - 1)) • ∫ t in Ioi (0 : ℝ), φ t * g (r * t)) μ
    simp_rw [hT]
    exact hFint.integral_prod_left
  · show (∫ r in Ioi (0 : ℝ), ((r : ℂ) ^ (z - 1)) • ∫ t in Ioi (0 : ℝ), φ t * g (r * t)) = _
    simp_rw [hT]
    rw [show (∫ r, ∫ t, F (r, t) ∂μ ∂μ) = ∫ t, ∫ r, F (r, t) ∂μ ∂μ from
      integral_integral_swap (f := fun r t => F (r, t)) (by simpa only [Function.uncurry_def] using hFint)]
    have hinner : ∀ {t : ℝ}, 0 < t → ∫ r, F (r, t) ∂μ = ((t : ℂ) ^ (-z) * φ t) * mellin g z := by
      intro t ht
      have := mellin_comp_mul_right g z ht
      simp only [mellin, smul_eq_mul] at this
      show (∫ r in Ioi (0 : ℝ), ((r : ℂ) ^ (z - 1)) * (φ t * g (r * t))) = _
      rw [show (fun r : ℝ => ((r : ℂ) ^ (z - 1)) * (φ t * g (r * t))) =
          fun r : ℝ => φ t * (((r : ℂ) ^ (z - 1)) * g (r * t)) from funext fun r => mul_left_comm _ _ _,
        integral_const_mul, this, show mellin g z = ∫ r in Ioi (0 : ℝ), ((r : ℂ) ^ (z - 1)) * g r from by
          simp only [mellin, smul_eq_mul]]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hinner ht), integral_mul_const]
    congr 1
    simp only [mellin, smul_eq_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 2
    ring

end Ws23K3

theorem solution
    (φ g : ℝ → ℂ) (z : ℂ)
    (hφm : AEStronglyMeasurable φ (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hgm : AEStronglyMeasurable g (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hφ : MellinConvergent φ (1 - z)) (hg : MellinConvergent g z) :
    MellinConvergent (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z ∧
      mellin (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z = mellin φ (1 - z) * mellin g z := by

  set g' : ℝ → ℂ := hgm.mk g with hg'
  have hgM : Measurable g' := hgm.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), g u = g' u := hgm.ae_eq_mk
  have hgz : MellinConvergent g' z := by
    refine (hg : Integrable _ _).congr ?_
    filter_upwards [hae] with u hu
    rw [hu]
  have hmg : mellin g' z = mellin g z := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    rw [hu]
  have hT : ∀ r ∈ Ioi (0 : ℝ), (∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) = ∫ t in Set.Ioi (0 : ℝ), φ t * g' (r * t) := by
    intro r hr
    refine integral_congr_ae ?_
    filter_upwards [Ws23K3.ae_restrict_comp_mul hae hr] with t ht
    rw [ht]
  obtain ⟨h1, h2⟩ := Ws23K3.core φ g' z hφm hgM hφ hgz
  refine ⟨?_, ?_⟩
  · refine (integrableOn_congr_fun (fun r hr => ?_) measurableSet_Ioi).2 h1
    show ((r : ℂ) ^ (z - 1)) • (∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) = ((r : ℂ) ^ (z - 1)) • ∫ t in Set.Ioi (0 : ℝ), φ t * g' (r * t)
    rw [hT r hr]
  · rw [← hmg, ← h2]
    simp only [mellin]
    exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [hT r hr]

#print axioms solution

end S_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin
end P2MW
export P2MW.S_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin (solution)
