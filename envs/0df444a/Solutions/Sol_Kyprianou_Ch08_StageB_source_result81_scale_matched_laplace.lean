-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_scale_matched_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:15:13.703501+00:00
-- url     : https://prove2.me/submissions/5f3648d3-174e-45df-abaf-baa50311a204

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real

open AvramDividend.Classical
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ψ w : ℝ → ℝ) (q : ℝ) (hφ : 0 < Phi ψ q)
    (hW : IsQScale ψ q w) (ν : Measure ℝ)
    (β : ℝ) (hβφ : Phi ψ q < β)
    (hcI : IntegrableOn (fun y : ℝ => Real.exp (-β * y) * cdf ν y) (Ioi 0))
    (hcLap : (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * cdf ν y) =
      (1 / β) * ((q / Phi ψ q) * ((Phi ψ q - β) / (q - ψ β)))) :
    let f := fun y => q / Phi ψ q * w y
    let g := fun y => cdf ν y + q * integratedScale w y
    IntegrableOn (fun y : ℝ => Real.exp (-β * y) * f y) (Ioi 0) ∧
      IntegrableOn (fun y : ℝ => Real.exp (-β * y) * g y) (Ioi 0) ∧
      (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * f y) =
        ∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * g y := by
  intro f g
  have hLargest := hW.1
  have hWlap := hW.2.2.2.2.2
  let φ := Phi ψ q
  let J := integratedScale w
  have hβ : 0 < β := hφ.trans hβφ
  have hgap : ψ β ≠ q := fun hh =>
    (not_le_of_gt hβφ) (hLargest.2.2 β ⟨hβ.le, hh⟩)
  obtain ⟨hw, hwLap⟩ := hWlap β hβ.le hβφ
  have hprim := positive_laplace_interval_primitive_real w β hβ
    (by simpa only [neg_mul] using hw)
  have hJint : IntegrableOn (fun y : ℝ => Real.exp (-β * y) * J y) (Ioi 0) := by
    simpa only [J, integratedScale, neg_mul] using hprim.1
  have hJlap : (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * J y) = (ψ β - q)⁻¹ / β := by
    calc
      _ = (∫ y in Ioi (0 : ℝ), Real.exp (-β * y) * w y) / β := by
        simpa only [J, integratedScale, neg_mul] using hprim.2
      _ = _ := by rw [hwLap]
  have heF : (fun y : ℝ => Real.exp (-β * y) * f y) =
      (fun y => (q / φ) * (Real.exp (-β * y) * w y)) := by
    funext y
    dsimp [f]
    ring
  have heG : (fun y : ℝ => Real.exp (-β * y) * g y) =
      (fun y => Real.exp (-β * y) * cdf ν y + q * (Real.exp (-β * y) * J y)) := by
    funext y
    dsimp [g, J]
    ring
  rw [heF, heG]
  refine ⟨hw.integrable.const_mul _, hcI.integrable.add (hJint.integrable.const_mul _), ?_⟩
  rw [integral_const_mul, integral_add hcI.integrable (hJint.integrable.const_mul q),
    integral_const_mul, hwLap, hcLap, hJlap]
  simp only [φ]
  field_simp [hφ.ne', hβ.ne', sub_ne_zero.mpr hgap, sub_ne_zero.mpr hgap.symm] <;> ring
