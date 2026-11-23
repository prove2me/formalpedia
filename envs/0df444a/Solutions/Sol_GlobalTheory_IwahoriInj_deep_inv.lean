-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.deep_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:30.97607+00:00
-- url     : https://prove2.me/submissions/5f241d20-1c33-4604-9bfb-ec6b769167c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_GlobalTheory_IwahoriInj_deep_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {u : k} (h1 : ¬ Deep 1 u) : u ≠ 0 ∧ Deep 0 u⁻¹ := by
  rw [deep_one_iff, not_lt] at h1
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [deep_zero_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ h1
end GlobalTheory.IwahoriInj
