-- Prove2me | solution 1 for GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:11:51.957788+00:00
-- url     : https://prove2.me/submissions/844c59b6-ca5f-407e-9b82-ac81a187dfa4

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
import Theorems.Thm_GlobalTheory_QuotientMeasureSigmaFinite_sigmaFinite_of_pos_lintegral_ne_top
import Theorems.Thm_GlobalTheory_QuotientMeasureSigmaFinite_measurable_mul_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.QuotientMeasureSigmaFinite
namespace GlobalTheory.QuotientMeasureSigmaFinite
theorem _root_.solution {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨h, hpos, hmeas, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hne : ∀ y, h y ≠ 0 := fun y => (hpos y).ne'
  have hF : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ((h (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) : NNReal) : ℝ≥0∞) :=
    (measurable_coe_nnreal_ennreal.comp hmeas).comp (measurable_mul_pair k r)
  have hq' : ∫⁻ x, (h x : ℝ≥0∞) ∂μG =
      ∫⁻ x, (∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS) ∂ν :=
    hq _ (measurable_coe_nnreal_ennreal.comp hmeas)

  refine sigmaFinite_of_pos_lintegral_ne_top
    (g := fun x => ∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS)
    hF.lintegral_prod_right' ?_ ?_
  · intro x hx
    have hfm : Measurable fun s : Formalism.QuantumDeterminants.Mt k r =>
        ((h (fun i j => (Matrix.of s * Matrix.of x) i j) : NNReal) : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp hmeas).comp
        (measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => by
          simp only [Matrix.mul_apply, Matrix.of_apply]
          fun_prop)
    rw [lintegral_eq_zero_iff hfm] at hx
    apply hS
    rw [← Measure.measure_univ_eq_zero]
    have h0 := ae_iff.1 hx
    simpa [hne] using h0
  · rw [← hq']
    exact (hint.trans ENNReal.one_lt_top).ne
end GlobalTheory.QuotientMeasureSigmaFinite
