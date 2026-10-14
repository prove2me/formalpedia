-- Prove2me | solution 1 for MeasureTheory.eLpNorm_convolution_le_of_nonneg_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:02:31.060656+00:00
-- url     : https://prove2.me/submissions/560f5d0c-4b6a-4130-9809-c9afbbe5b783

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Theorems.Thm_MeasureTheory_eLpNorm_integral_le_lintegral

open MeasureTheory ContinuousLinearMap
open scoped Convolution

theorem solution {n : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : MemLp d p volume) :
    eLpNorm (ρ ⋆[lsmul ℝ ℝ, volume] d) p volume ≤ eLpNorm d p volume := by
  let F := fun x y => ρ y * d (x - y)
  have hρi : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hc := hρs.convolutionExists_left (lsmul ℝ ℝ) hρc (hd.locallyIntegrable hp)
  have hFi (x) : Integrable (F x) volume := (hc x).integrable
  have hF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    exact (hρi.aestronglyMeasurable.convolution_integrand
      (μ := volume) (lsmul ℝ ℝ) hd.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun z => by
        simp only [F, Function.uncurry, lsmul_apply, smul_eq_mul])
  have hav := MeasureTheory.eLpNorm_integral_le_lintegral volume volume hp hptop F hF
    (Filter.Eventually.of_forall hFi)
  change eLpNorm (ρ ⋆[lsmul ℝ ℝ, volume] d) p volume ≤ _ at hav
  refine hav.trans_eq ?_
  have heq (y) : eLpNorm (fun x => F x y) p volume =
      ENNReal.ofReal (ρ y) * eLpNorm d p volume := by
    change eLpNorm ((ρ y) • (fun x => d (x - y))) p volume = _
    rw [eLpNorm_const_smul]
    have hn : ‖ρ y‖ₑ = ENNReal.ofReal (ρ y) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hρ0 y)]
    rw [hn]
    congr 1
    exact eLpNorm_comp_measurePreserving hd.aestronglyMeasurable
      (measurePreserving_sub_right volume y)
  simp_rw [heq]
  rw [lintegral_mul_const _ hρc.measurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρ0),
    hρ1, ENNReal.ofReal_one, one_mul]
