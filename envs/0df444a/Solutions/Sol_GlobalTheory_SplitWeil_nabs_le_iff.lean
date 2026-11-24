-- Prove2me | solution 1 for GlobalTheory.SplitWeil.nabs_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:06.585168+00:00
-- url     : https://prove2.me/submissions/05392c4d-21e7-4ba6-afdf-7e4cdc136ba3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_le_of_valuation_le
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_lt_of_valuation_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (x y : kˣ) : nabs k x ≤ nabs k y ↔ valuation k (x : k) ≤ valuation k (y : k) :=
  ⟨fun h => not_lt.mp fun h' => absurd h (not_le.mpr (nabs_lt_of_valuation_lt h')),
    nabs_le_of_valuation_le⟩
end GlobalTheory.SplitWeil
