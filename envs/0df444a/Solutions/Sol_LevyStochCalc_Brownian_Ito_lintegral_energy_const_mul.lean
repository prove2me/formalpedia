-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:51:39.631806+00:00
-- url     : https://prove2.me/submissions/9e88f041-632f-4963-a629-39a29ac3db3d

import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Additivity of the L² Itô integral in the integrand

The Itô isometry and the isometry of differences determine every squared `L²`-distance among
`∫ H₁ dW`, `∫ H₂ dW` and `∫ (H₁ + H₂) dW` in terms of the energies of `H₁`, `H₂`, `H₁ + H₂` and
`H₁ − H₂`. The parallelogram law for those energies then forces
`∫ (H₁ + H₂) dW = ∫ H₁ dW + ∫ H₂ dW` almost everywhere.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {H₁ H₂ : Ω → ℝ → ℝ}


omit [IsProbabilityMeasure P] in

theorem _root_.solution {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (c T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hc : (‖c‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (c ^ 2) := by
    rw [← ENNReal.coe_pow]
    congr 1
    apply NNReal.eq
    simp [Real.norm_eq_abs, sq_abs, Real.toNNReal_of_nonneg (sq_nonneg c)]
  simp_rw [nnnorm_mul, ENNReal.coe_mul, mul_pow, hc]
  have hω (ω : Ω) : (∫⁻ s in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (c ^ 2) * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) =
    ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    apply lintegral_const_mul
    have h : Measurable (fun s => H ω s) := hm.comp (measurable_const.prodMk measurable_id)
    exact h.nnnorm.coe_nnreal_ennreal.pow_const 2
  simp_rw [hω]
  apply lintegral_const_mul
  exact (hm.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
