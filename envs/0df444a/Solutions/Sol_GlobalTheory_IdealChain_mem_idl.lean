-- Prove2me | solution 1 for GlobalTheory.IdealChain.mem_idl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:35.641386+00:00
-- url     : https://prove2.me/submissions/57cdd125-0087-4460-8274-bdfa049dac70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IdealChain
theorem _root_.solution {b : kˣ} {x : k} : x ∈ idl b ↔ valuation k x ≤ valuation k (b : k) := by
  have hb : valuation k (b : k) ≠ 0 := by simp
  rw [idl, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, rfl⟩
    change valuation k ((s : k) * b) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' s.2
  · intro h
    refine ⟨⟨x / b, ?_⟩, ?_⟩
    · change valuation k (x / b) ≤ 1
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    · change x / b * b = x
      simp
end GlobalTheory.IdealChain
