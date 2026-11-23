-- Prove2me | solution 1 for GlobalTheory.SatakeFlip.cosetMap_cosetMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:10.636823+00:00
-- url     : https://prove2.me/submissions/11f7e79c-ef95-4f1f-aab7-d7512c271c1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Theorems.Thm_GlobalTheory_SatakeFlip_invRevT_invRevT
import Theorems.Thm_GlobalTheory_SatakeFlip_cosetMap_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound Matrix
open GlobalTheory GlobalTheory.SatakeFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.SatakeFlip
theorem _root_.solution (c : GL (Fin n) k ⧸ KO k (Fin n)) : cosetMap (cosetMap c) = c := by
  induction c using QuotientGroup.induction_on with
  | H g => rw [cosetMap_mk, cosetMap_mk, invRevT_invRevT]
end GlobalTheory.SatakeFlip
