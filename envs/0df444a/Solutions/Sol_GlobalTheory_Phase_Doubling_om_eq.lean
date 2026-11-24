-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.om_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:28:18.29681+00:00
-- url     : https://prove2.me/submissions/76260e43-e936-4506-b873-d65f4be40fb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Theorems.Thm_GlobalTheory_Phase_Doubling_dot_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Doubling
noncomputable section
variable {n g : ℕ}
namespace GlobalTheory.Phase.Doubling
theorem _root_.solution (y y' : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    om y y' = om (comp 0 y) (comp 0 y') + om (comp 1 y) (comp 1 y') := by
  simp only [om, Fin.sum_univ_two, dot_row, Finset.sum_sub_distrib]
  exact add_sub_add_comm _ _ _ _
end GlobalTheory.Phase.Doubling
