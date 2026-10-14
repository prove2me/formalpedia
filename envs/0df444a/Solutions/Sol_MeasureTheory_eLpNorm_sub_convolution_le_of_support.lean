-- Prove2me | solution 1 for MeasureTheory.eLpNorm_sub_convolution_le_of_support
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T14:48:28.682477+00:00
-- url     : https://prove2.me/submissions/87a9381f-ae69-4a0e-a723-44505f4f3ba3

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Theorems.Thm_MeasureTheory_eLpNorm_integral_le_lintegral

open MeasureTheory ContinuousLinearMap
open scoped Convolution

theorem solution {n : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : MemLp d p volume)
    (ε : ENNReal)
    (hε : ∀ y ∈ Function.support ρ,
      eLpNorm (fun x => d (x - y) - d x) p volume ≤ ε) :
    eLpNorm (d - (ρ ⋆[lsmul ℝ ℝ, volume] d)) p volume ≤ ε := by
  let F := fun x y => ρ y * (d (x - y) - d x)
  have hρi : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hc := hρs.convolutionExists_left (lsmul ℝ ℝ) hρc (hd.locallyIntegrable hp)
  have hFi (x) : Integrable (F x) volume := by
    have h := (hc x).integrable
    change Integrable (fun y => ρ y * d (x - y)) volume at h
    exact (h.sub (hρi.mul_const (d x))).congr
      (Filter.Eventually.of_forall fun y => by simp only [F, Pi.sub_apply, mul_sub])
  have hF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h₁ := hρi.aestronglyMeasurable.convolution_integrand
      (μ := volume) (lsmul ℝ ℝ) hd.aestronglyMeasurable
    have h₂ : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ρ z.2 * d z.1)
        (volume.prod volume) :=
      (hρi.aestronglyMeasurable.comp_snd (μ := volume)).mul
        (hd.aestronglyMeasurable.comp_fst (ν := volume))
    exact (h₁.sub h₂).congr (Filter.Eventually.of_forall fun z => by
      simp only [F, Function.uncurry, Pi.sub_apply, mul_sub, lsmul_apply, smul_eq_mul])
  have heq : (fun x => ∫ y, F x y) = (ρ ⋆[lsmul ℝ ℝ, volume] d) - d := by
    funext x
    have h := (hc x).integrable
    change Integrable (fun y => ρ y * d (x - y)) volume at h
    simp only [F, mul_sub, integral_sub h (hρi.mul_const (d x)),
      integral_mul_const, hρ1, one_mul, Pi.sub_apply, convolution_def,
      lsmul_apply, smul_eq_mul]
  have hav := MeasureTheory.eLpNorm_integral_le_lintegral volume volume hp hptop F hF
    (Filter.Eventually.of_forall hFi)
  rw [heq, eLpNorm_sub_comm] at hav
  refine hav.trans ?_
  calc
    (∫⁻ y, eLpNorm (fun x => F x y) p volume) ≤ ∫⁻ y, ENNReal.ofReal (ρ y) * ε := by
      apply lintegral_mono
      intro y
      by_cases hy : ρ y = 0
      · simp [F, hy]
      · have hn : ‖ρ y‖ₑ = ENNReal.ofReal (ρ y) := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hρ0 y)]
        change eLpNorm ((ρ y) • (fun x => d (x - y) - d x)) p volume ≤ _
        rw [eLpNorm_const_smul, hn]
        exact mul_le_mul_right (hε y hy) _
    _ = ε := by
      rw [lintegral_mul_const _ hρc.measurable.ennreal_ofReal,
        ← ofReal_integral_eq_lintegral_ofReal hρi
        (Filter.Eventually.of_forall hρ0), hρ1, ENNReal.ofReal_one, one_mul]
