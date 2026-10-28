-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_abs_le_sqrt_of_lintegral_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:25.292577+00:00
-- url     : https://prove2.me/submissions/f2eeb055-12a2-4e71-b356-bea251037699

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoMartingaleRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaScalar
import Theorems.Thm_LevyStochCalc_integral_abs_le_sqrt_of_integral_sq_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A square-integrable function lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top {P' : Measure Ω} {f : Ω → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f P')
    (h : ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P' < ⊤) : MemLp f 2 P' := by
  refine ⟨hf, ?_⟩
  by_contra hcon
  have htop : MeasureTheory.eLpNorm f 2 P' = ⊤ := top_le_iff.mp (not_lt.mp hcon)
  rw [← eLpNorm_two_rpow_eq_lintegral_sq f, htop,
    ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  exact lt_irrefl _ h
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The square of a real number's extended norm is the extended value of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_enn_nnnorm_eq_ofReal_sq (x : ℝ) :
    ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
    rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
    exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
  rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaScalar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- From an `L²` bound in extended form, the first absolute moment is at most `√V`. -/
theorem solution {P : Measure Ω} [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.AEStronglyMeasurable g P) {V : ℝ} (hV0 : 0 ≤ V)
    (hle : ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal V) :
    MeasureTheory.Integrable g P ∧ ∫ ω, |g ω| ∂P ≤ Real.sqrt V := by
  have hmem : MeasureTheory.MemLp g 2 P :=
    LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hg (lt_of_le_of_lt hle (by simp))
  have hint : MeasureTheory.Integrable g P := hmem.integrable (by norm_num)
  have hsq : MeasureTheory.Integrable (fun ω => g ω ^ 2) P := by
    have hmul := hmem.integrable_mul hmem
    have hfun : (fun ω => g ω ^ 2) = g * g := by
      funext ω
      simp [pow_two]
    rw [hfun]
    exact hmul
  have hsqnn : ∀ ω : Ω, (0 : ℝ) ≤ g ω ^ 2 := fun ω => sq_nonneg _
  have hkey : ENNReal.ofReal (∫ ω, g ω ^ 2 ∂P) ≤ ENNReal.ofReal V := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsq
      (Filter.Eventually.of_forall hsqnn)]
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hle
    exact (LevyStochCalc.Brownian.Ito.sq_enn_nnnorm_eq_ofReal_sq (g ω)).symm
  refine ⟨hint, LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le_readable hint.abs hsq ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff hV0).mp hkey
