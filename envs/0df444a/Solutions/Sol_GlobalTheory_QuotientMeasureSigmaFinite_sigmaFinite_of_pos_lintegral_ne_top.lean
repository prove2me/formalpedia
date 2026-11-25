-- Prove2me | solution 1 for GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_pos_lintegral_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:34.849272+00:00
-- url     : https://prove2.me/submissions/5f3159df-1378-4e68-865d-243fbdc905b9

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
theorem _root_.solution {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℝ≥0∞} (hg : Measurable g) (hpos : ∀ x, g x ≠ 0) (hfin : ∫⁻ x, g x ∂ν ≠ ∞) :
    SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    have h0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have h1 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    exact (meas_ge_le_lintegral_div hg.aemeasurable h0 h1).trans_lt (ENNReal.div_lt_top hfin h0)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x)
    refine Set.mem_sUnion.2 ⟨_, ⟨n, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le
end GlobalTheory.QuotientMeasureSigmaFinite
