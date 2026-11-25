-- Prove2me | solution 1 for GlobalTheory.HyperboloidPolar.hypAmb_conc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:19.217647+00:00
-- url     : https://prove2.me/submissions/dccba5f6-5cea-4f75-9c0b-e3ca6977b16d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsWInvO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_ConstPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TransW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HyperboloidInvariantMeasurePolarForm
import Theorems.Thm_GlobalTheory_HyperboloidPolar_opVec_inWb
import Theorems.Thm_GlobalTheory_HyperboloidPolar_continuous_opVec
import Theorems.Thm_GlobalTheory_HyperboloidPolar_herm_opVec
import Theorems.Thm_GlobalTheory_HyperboloidPolar_herm_self_eq
import Theorems.Thm_PI_RhsWLim_W_hypLF
import Theorems.Thm_PI_RhsWLim_W_hypS_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.HyperboloidPolar
open PI.RhsWLim PI.RhsWLim.W
variable {k r : ℕ}
namespace GlobalTheory.HyperboloidPolar
theorem _root_.solution {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    hypAmb k r (Tz k r z') {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 := by
  have hc : IsClosed {v : Fin (2 * r + k + 1) → ℂ |
      inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z'} := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} =
          ⋂ i : Fin (2 * r + k + 1), ⋂ _ : (i.val < r ∨ r + k < i.val), {v | v i = 0} := by
        ext v
        simp only [inWb, Set.mem_iInter]
        rfl
      show IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v}
      rw [this]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
    · unfold herm
      exact continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hm : MeasurableSet {v : Fin (2 * r + k + 1) → ℂ |
      ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} := hc.measurableSet.compl
  rw [hypAmb, Measure.map_apply continuous_opVec.measurable hm]
  refine measure_mono_null ?_ (hypLF k _ hT').1
  intro p hp hS
  apply hp
  refine ⟨opVec_inWb p, ?_⟩
  rw [herm_opVec, herm_self_eq hz', (hypS_iff _ p).1 hS]
end GlobalTheory.HyperboloidPolar
