-- Prove2me | solution 1 for GlobalTheory.QuotientMeasureSigmaFinite.measurable_mul_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:34.065585+00:00
-- url     : https://prove2.me/submissions/45b3d4f5-8d83-4b02-94ed-7556521fbf4e

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop

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
theorem _root_.solution (k r : ℕ) :
    Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop
end GlobalTheory.QuotientMeasureSigmaFinite
