-- Prove2me | solution 1 for GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:58.002215+00:00
-- url     : https://prove2.me/submissions/4d612400-31d5-475f-9bb7-852dfda0819e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnits
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Theorems.Thm_GlobalTheory_CMVal_OrderUnits_orderC_units


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  first | exact @GlobalTheory.CMVal.OrderUnits.orderC_units | exact GlobalTheory.CMVal.OrderUnits.orderC_units | (intros; apply GlobalTheory.CMVal.OrderUnits.orderC_units <;> assumption)
end _root_.GlobalTheory.T
