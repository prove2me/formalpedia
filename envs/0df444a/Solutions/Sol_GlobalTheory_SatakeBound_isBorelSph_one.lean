-- Prove2me | solution 1 for GlobalTheory.SatakeBound.isBorelSph_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:16.071869+00:00
-- url     : https://prove2.me/submissions/bab4e8dc-9b02-4ef6-862d-3f9e3b325de0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory GlobalTheory.SatakeBound
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.SatakeBound
theorem _root_.solution : IsBorelSph k (n := n) (fun _ => 1) fun _ => 1 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩
end GlobalTheory.SatakeBound
