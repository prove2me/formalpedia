-- Prove2me | solution 1 for MeasureTheory.tendsto_integral_mul_of_eLpNorm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T22:12:12.856065+00:00
-- url     : https://prove2.me/submissions/446b8588-5174-4729-b981-9838e8a54d65

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
open MeasureTheory Filter
open scoped ENNReal Topology
set_option autoImplicit false

theorem solution {n : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsLocallyFiniteMeasure μ]
    (u : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : ∀ j, MemLp (u j) p μ) (hv : MemLp v p μ)
    (hlim : Tendsto (fun j => eLpNorm (u j - v) p μ) atTop (𝓝 0))
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun j => ∫ x, u j x * ψ x ∂μ) atTop (𝓝 (∫ x, v x * ψ x ∂μ)) := by
  let q : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have hinv : p⁻¹ ≤ 1 := by simpa using (ENNReal.inv_le_inv.mpr hp)
  let : ENNReal.HolderConjugate p q := ⟨by
    simpa only [q, inv_inv, inv_one] using add_tsub_cancel_of_le hinv⟩
  have hψp : MemLp ψ q μ := hψ.memLp_of_hasCompactSupport hc
  have hi (j : ℕ) : Integrable (fun x => u j x * ψ x) μ :=
    memLp_one_iff_integrable.mp (hψp.mul' (hu j))
  apply tendsto_integral_of_L1' (fun x => v x * ψ x)
    (hv.1.mul hψ.aestronglyMeasurable) (Eventually.of_forall hi)
  have hb : Tendsto (fun j => eLpNorm (u j - v) p μ * eLpNorm ψ q μ) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul_const hlim (Or.inr hψp.eLpNorm_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
  intro j
  change eLpNorm ((fun x => u j x * ψ x) - (fun x => v x * ψ x)) 1 μ ≤
    eLpNorm (u j - v) p μ * eLpNorm ψ q μ
  calc
    _ = eLpNorm ((u j - v) • ψ) 1 μ := by
      congr 1
      ext x
      simp [sub_mul]
    _ ≤ _ := eLpNorm_smul_le_mul_eLpNorm hψp.1 ((hu j).sub hv).1
