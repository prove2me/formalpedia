-- Prove2me | solution 1 for GlobalTheory.IdealChain.idl_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:03:40.24472+00:00
-- url     : https://prove2.me/submissions/1972168e-05f2-495a-a2f6-bb3fd644bd6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_IdealChain_mem_idl

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
theorem _root_.solution {a b : kˣ} : idl a = idl b ↔ valuation k (a : k) = valuation k (b : k) := by
  constructor
  · intro h
    exact le_antisymm (mem_idl.1 (h ▸ mem_idl.2 le_rfl)) (mem_idl.1 (h ▸ mem_idl.2 le_rfl))
  · intro h
    ext x
    rw [mem_idl, mem_idl, h]
end GlobalTheory.IdealChain
