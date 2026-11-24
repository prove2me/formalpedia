-- Prove2me | solution 1 for GlobalTheory.IdealChain.act_stdLat_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:37:19.060831+00:00
-- url     : https://prove2.me/submissions/0c07bf9d-522f-443a-9ed2-4626e7f8613c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_IdealChain_mem_act
import Theorems.Thm_GlobalTheory_LatPair_maps_stdLat_iff
import Theorems.Thm_GlobalTheory_StepData_mem_KO


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
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
namespace GlobalTheory.IdealChain
theorem _root_.solution {g : GL ι k} : act g (stdLat k ι) = stdLat k ι ↔ g ∈ KO k ι := by
  rw [mem_KO]
  constructor
  · intro h
    refine ⟨maps_stdLat_iff.1 fun y hy => ?_, maps_stdLat_iff.1 fun y hy => ?_⟩
    · rw [← h]
      exact ⟨y, hy, rfl⟩
    · rw [← h] at hy
      exact mem_act.1 hy
  · rintro ⟨h1, h2⟩
    ext v
    rw [mem_act]
    refine ⟨fun hv => ?_, fun hv => maps_stdLat_iff.2 h2 v hv⟩
    simpa using maps_stdLat_iff.2 h1 _ hv
end GlobalTheory.IdealChain
