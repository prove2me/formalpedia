-- Prove2me | solution 1 for GlobalTheory.StepData.valuation_det_of_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:52.017598+00:00
-- url     : https://prove2.me/submissions/c362d5a5-06f4-42ae-a533-ca0a1dfc26b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.StepData
theorem _root_.solution {g : GL n k} (h : g ∈ KO k n) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  obtain ⟨u, rfl⟩ := h
  have hu : IsUnit u.val.det := (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have := (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.1 hu
  convert this using 2
  exact ((algebraMap 𝒪[k] k).map_det u.val).symm
end GlobalTheory.StepData
