-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.eLpNorm_one_mul_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:13.916997+00:00
-- url     : https://prove2.me/submissions/7f601b37-82e9-4ce8-b658-0d9ee29781d6

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionConvergence.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **L² Hölder product.** `‖f·g‖₁ ≤ ‖f‖₂·‖g‖₂` (Cauchy–Schwarz). The
conjunct-2 (quadratic-variation) limit needs `aₙ²→a²` in `L¹` from `aₙ→a` in
`L²`, via `aₙ²−a² = (aₙ−a)(aₙ+a)` and this bound. -/
lemma solution {μ : MeasureTheory.Measure Ω} {f g : Ω → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (f * g) 1 μ
      ≤ MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
  have hpq : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  calc ∫⁻ x, ‖(f * g) x‖ₑ ∂μ
      = ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ := by
        refine lintegral_congr (fun x => ?_); rw [Pi.mul_apply, enorm_mul]
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
        * (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.enorm hg.enorm
    _ = MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
            MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
        norm_num
