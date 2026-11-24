-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.exists_deep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:34.991729+00:00
-- url     : https://prove2.me/submissions/c4ad0c74-4fe1-4199-835c-d49b7195afd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit

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
theorem _root_.solution (a : ℤ) : ∃ c : k, c ≠ 0 ∧ Deep a c ∧ Deep (-a) c⁻¹ := by
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k ^ a)
  refine ⟨c, fun h => ?_, hc.le, ?_⟩
  · rw [h, map_zero] at hc
    exact (zpow_pos unif_pos a).ne hc
  · simp [Deep, hc]
end GlobalTheory.IwahoriInj
