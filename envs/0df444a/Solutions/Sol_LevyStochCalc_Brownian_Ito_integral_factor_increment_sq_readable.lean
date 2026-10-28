-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_factor_increment_sq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:54.439084+00:00
-- url     : https://prove2.me/submissions/505bcf54-c72d-4968-8bf0-611a01690ee1

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
/-- `∫ (W_b − W_a)² = b − a` for `0 ≤ a < b`. -/
lemma LevyStochCalc.Brownian.Ito.brownian_incr_sq_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P)
        = ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2) _)).symm,
    W.increment_gaussian ha hab]
  exact LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨b - a, by linarith⟩
/-- **Conditional diagonal.** For a bounded `ℱ_a`-measurable factor `g`,
`∫ g · (W_b − W_a)² = (∫ g) · (b − a)` — the increment square is independent of the
`ℱ_a`-measurable `g`, with second moment `b − a`. -/
lemma solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a)
      (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * (b - a) := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW
  have hΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have hg_m : Measurable g :=
    (hg_meas.mono (ℱ.le a)).measurable
  -- IndepFun g ΔW
  have h_indep_F := hℱ.indep ha hab
  have hg_comap_le : MeasurableSpace.comap g inferInstance ≤ ℱ a :=
    hg_meas.measurable.comap_le
  have h_indep_g_ΔW : ProbabilityTheory.IndepFun g ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]; intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F
    exact h_indep_F u v (hg_comap_le u hu) hv
  have h_indep_g_ΔWsq : ProbabilityTheory.IndepFun g (fun ω => (ΔW ω) ^ 2) P := by
    have := h_indep_g_ΔW.comp measurable_id (measurable_id.pow_const 2)
    simpa [Function.comp_def] using this
  rw [show (fun ω => g ω * (W.W b ω - W.W a ω) ^ 2) = g * (fun ω => (ΔW ω) ^ 2) from rfl,
    h_indep_g_ΔWsq.integral_mul_eq_mul_integral hg_m.aestronglyMeasurable
    ((hΔW_meas.pow_const 2).aestronglyMeasurable), LevyStochCalc.Brownian.Ito.brownian_incr_sq_integral W ha hab]
