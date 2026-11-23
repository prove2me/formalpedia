-- Prove2me | solution 1 for GlobalTheory.SatakeFlip.cosetMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:47.073541+00:00
-- url     : https://prove2.me/submissions/60da2d57-75e8-47d5-a689-f024fc3b8b61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv

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
theorem _root_.solution (g : GL (Fin n) k) :
    cosetMap (g : GL (Fin n) k ⧸ KO k (Fin n)) = (invRevT g : GL (Fin n) k) := rfl
end GlobalTheory.SatakeFlip
